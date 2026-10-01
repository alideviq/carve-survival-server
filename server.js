import crypto from 'node:crypto';
import { EventEmitter } from 'node:events';
import http from 'node:http';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const GAME_CONFIG = Object.freeze({
  MIN_PLAYERS: 2,
  MAX_PLAYERS: 6,
  GRID_SIZE: 3,
  CELL_COUNT: 27,
  MEMORIZE_SECONDS: 6,
  CARVE_SECONDS_BY_PLAYERS: Object.freeze({ 2: 20, 3: 19, 4: 18, 5: 17, 6: 16 }),
  REQUIRED_SCORE_BY_PLAYERS: Object.freeze({ 2: 50, 3: 55, 4: 60, 5: 65, 6: 70 }),
  PLANNED_ROUNDS_BY_PLAYERS: Object.freeze({ 2: 5, 3: 5, 4: 6, 5: 6, 6: 7 }),
  RECONNECT_GRACE_MS: 45_000,
  RESULT_MS: 3_800
});

function getCarveSeconds(count) { return GAME_CONFIG.CARVE_SECONDS_BY_PLAYERS[count] ?? 20; }
function getRequiredScore(count) { return GAME_CONFIG.REQUIRED_SCORE_BY_PLAYERS[count] ?? 50; }
function getPlannedRounds(count) { return GAME_CONFIG.PLANNED_ROUNDS_BY_PLAYERS[count] ?? 5; }



function hashSeed(seed) {
  let x = seed | 0;
  x ^= x << 13; x ^= x >>> 17; x ^= x << 5;
  return x >>> 0;
}
function rng(seed) {
  let s = hashSeed(seed) || 0x9e3779b9;
  return () => { s = (s * 1664525 + 1013904223) >>> 0; return s / 0x100000000; };
}

function generatePattern(seed) {
  const random = rng(seed);
  const cells = Array(GAME_CONFIG.CELL_COUNT).fill(0);
  const targetCount = 9 + Math.floor(random() * 6);
  const neighbours = (i) => {
    const x = i % 3, y = Math.floor(i / 3) % 3, z = Math.floor(i / 9);
    const out = [];
    const add = (nx, ny, nz) => {
      if (nx >= 0 && nx < 3 && ny >= 0 && ny < 3 && nz >= 0 && nz < 3) out.push(nx + ny * 3 + nz * 9);
    };
    add(x - 1, y, z); add(x + 1, y, z); add(x, y - 1, z); add(x, y + 1, z); add(x, y, z - 1); add(x, y, z + 1);
    return out;
  };
  cells[13] = 1;
  let carved = 1;
  while (carved < targetCount) {
    const frontier = [];
    for (let i = 0; i < cells.length; i++) if (cells[i]) for (const n of neighbours(i)) if (!cells[n]) frontier.push(n);
    const unique = [...new Set(frontier)];
    if (!unique.length) break;
    cells[unique[Math.floor(random() * unique.length)]] = 1;
    carved++;
  }
  return cells;
}

function scorePattern(player, target) {
  if (player.length !== target.length) throw new Error('Invalid pattern length');
  let targetCarved = 0, correctCarved = 0, wrongCarved = 0;
  for (let i = 0; i < target.length; i++) {
    const wanted = target[i] === 1;
    const isCarved = player[i] === 1;
    if (wanted) targetCarved++;
    if (wanted && isCarved) correctCarved++;
    if (!wanted && isCarved) wrongCarved++;
  }
  if (targetCarved === 0) return 100;
  // Match score is a deterministic F1-style score over the actual carved cells.
  // It rewards correct cuts (recall), penalizes extra cuts (precision), and gives
  // zero credit for an untouched cube instead of counting the easy empty cells.
  const predictedCarved = correctCarved + wrongCarved;
  if (predictedCarved === 0 || correctCarved === 0) return 0;
  const precision = correctCarved / predictedCarved;
  const recall = correctCarved / targetCarved;
  return Math.round((2 * precision * recall / (precision + recall)) * 100);
}



const GUID = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11';

function acceptKey(key) {
  return crypto.createHash('sha1').update(key + GUID).digest('base64');
}

class WebSocketConnection extends EventEmitter {
  constructor(socket) {
    super();
    this.socket = socket;
    this.buffer = Buffer.alloc(0);
    this.closed = false;
    socket.on('data', chunk => this.handleData(chunk));
    socket.on('close', () => this.finishClose());
    socket.on('error', () => this.finishClose());
  }

  send(event, data) {
    this.sendJson({ type: 'event', event, data });
  }

  ack(id, payload) {
    this.sendJson({ type: 'ack', id, ...payload });
  }

  sendJson(value) {
    if (this.closed || !this.socket.writable) return;
    const payload = Buffer.from(JSON.stringify(value));
    const header = [];
    header.push(0x81);
    if (payload.length < 126) header.push(payload.length);
    else if (payload.length < 65536) header.push(126, (payload.length >> 8) & 255, payload.length & 255);
    else {
      header.push(127);
      const len = BigInt(payload.length);
      for (let i = 7; i >= 0; i--) header.push(Number((len >> BigInt(i * 8)) & 0xffn));
    }
    this.socket.write(Buffer.concat([Buffer.from(header), payload]));
  }

  close() {
    if (this.closed) return;
    this.closed = true;
    try { this.socket.end(Buffer.from([0x88, 0x00])); } catch {}
  }

  handleData(chunk) {
    this.buffer = Buffer.concat([this.buffer, chunk]);
    while (true) {
      if (this.buffer.length < 2) return;
      const first = this.buffer[0], second = this.buffer[1];
      const opcode = first & 0x0f;
      const masked = Boolean(second & 0x80);
      let length = second & 0x7f;
      let offset = 2;
      if (length === 126) { if (this.buffer.length < 4) return; length = this.buffer.readUInt16BE(2); offset = 4; }
      else if (length === 127) { if (this.buffer.length < 10) return; const big = this.buffer.readBigUInt64BE(2); if (big > BigInt(Number.MAX_SAFE_INTEGER)) return this.close(); length = Number(big); offset = 10; }
      const maskOffset = masked ? 4 : 0;
      if (this.buffer.length < offset + maskOffset + length) return;
      let payload = this.buffer.subarray(offset + maskOffset, offset + maskOffset + length);
      if (masked) {
        const mask = this.buffer.subarray(offset, offset + 4);
        const copy = Buffer.alloc(length);
        for (let i = 0; i < length; i++) copy[i] = payload[i] ^ mask[i & 3];
        payload = copy;
      }
      this.buffer = this.buffer.subarray(offset + maskOffset + length);
      if (opcode === 0x8) return this.close();
      if (opcode === 0x9) { this.sendPong(payload); continue; }
      if (opcode !== 0x1) continue;
      try { this.emit('message', JSON.parse(payload.toString('utf8'))); } catch { this.send('system:error', { message: 'Invalid message.' }); }
    }
  }

  sendPong(payload) {
    const header = payload.length < 126 ? Buffer.from([0x8a, payload.length]) : Buffer.from([0x8a, 0]);
    this.socket.write(Buffer.concat([header, payload]));
  }

  finishClose() {
    if (this.closed) { this.emit('disconnect'); return; }
    this.closed = true;
    this.emit('disconnect');
  }
}

function upgradeToWebSocket(request, socket) {
  const key = request.headers['sec-websocket-key'];
  if (!key) { socket.destroy(); return null; }
  const headers = [
    'HTTP/1.1 101 Switching Protocols',
    'Upgrade: websocket',
    'Connection: Upgrade',
    `Sec-WebSocket-Accept: ${acceptKey(key)}`,
    '\r\n'
  ];
  socket.write(headers.join('\r\n'));
  return new WebSocketConnection(socket);
}



function sanitizeName(name) {
  const normalized = String(name ?? '').replace(/[\u0000-\u001F\u007F]/g, '').trim().slice(0, 18);
  return normalized || 'Player';
}

class GameManager {
  constructor(sendTo, broadcastToRoom) {
    this.sendTo = sendTo;
    this.broadcastToRoom = broadcastToRoom;
    this.rooms = new Map();
    this.playerRoom = new Map();
  }

  createRoom(connection, name, mode) {
    const code = this.makeRoomCode();
    const player = this.makePlayer(name, connection);
    const room = {
      code, hostId: player.id, mode: mode === 'teams' ? 'teams' : 'ffa', phase: 'lobby', round: 0,
      plannedRounds: 0, roundSeed: 0, target: [], phaseEndsAt: null, winnerPlayerIds: [], winnerTeam: null,
      players: new Map([[player.id, player]]), createdAt: Date.now()
    };
    this.rooms.set(code, room); this.playerRoom.set(player.id, code); connection.roomCode = code;
    this.emitRoom(room); return player.id;
  }

  joinRoom(connection, codeInput, name) {
    const code = String(codeInput ?? '').toUpperCase().trim();
    const room = this.rooms.get(code);
    if (!room) throw new Error('Room not found.');
    if (room.phase !== 'lobby') throw new Error('This room has already started.');
    if (room.players.size >= GAME_CONFIG.MAX_PLAYERS) throw new Error('Room is full.');
    const player = this.makePlayer(name, connection);
    room.players.set(player.id, player); this.playerRoom.set(player.id, code); connection.roomCode = code;
    this.assignTeams(room); this.emitRoom(room); return player.id;
  }

  reconnect(connection, playerId) {
    const room = this.roomForPlayer(playerId);
    if (!room) throw new Error('Reconnection session expired.');
    const player = room.players.get(playerId);
    if (!player || player.status === 'eliminated') throw new Error('This player is no longer in the match.');
    player.connection = connection; player.connected = true; player.status = 'connected';
    if (player.disconnectTimer) clearTimeout(player.disconnectTimer);
    connection.roomCode = room.code;
    this.emitRoom(room);
    if (room.phase === 'memorize') this.sendTo(player.connection, 'game:memorize', { round: room.round, pattern: room.target, durationMs: Math.max(0, room.phaseEndsAt - Date.now()), endsAt: room.phaseEndsAt });
    if (room.phase === 'carve') {
      this.sendTo(player.connection, 'game:carve', { round: room.round, endsAt: room.phaseEndsAt, requiredScore: getRequiredScore(room.players.size) });
      this.sendTo(player.connection, 'game:player-state', { carved: [...player.carved] });
      this.sendTo(player.connection, 'game:player-update', { playerId, score: scorePattern(player.carved, room.target), submitted: player.submitted, status: player.status });
    }
    if (room.phase === 'game-over') this.sendTo(player.connection, 'game:over', { mode: room.mode, winnerPlayerIds: room.winnerPlayerIds, winnerTeam: room.winnerTeam });
  }

  updateName(playerId, name) { const room = this.roomForPlayer(playerId); if (!room) return; room.players.get(playerId).name = sanitizeName(name); this.emitRoom(room); }
  updateMode(playerId, mode) { const room = this.roomForPlayer(playerId); if (!room || room.hostId !== playerId || room.phase !== 'lobby') return; room.mode = mode === 'teams' ? 'teams' : 'ffa'; this.assignTeams(room); this.emitRoom(room); }

  startRoom(playerId) {
    const room = this.roomForPlayer(playerId);
    if (!room || room.hostId !== playerId || room.phase !== 'lobby') return;
    const count = room.players.size;
    if (count < 2 || count > 6) throw new Error('The room needs between 2 and 6 players.');
    room.plannedRounds = getPlannedRounds(count); room.round = 1; room.roundSeed = Math.floor(Math.random() * 2_147_483_000); this.assignTeams(room); this.beginMemorize(room);
  }

  playAgain(playerId) {
    const room = this.roomForPlayer(playerId);
    if (!room || room.phase !== 'game-over') return;
    const active = [...room.players.values()].filter(p => p.connected);
    if (active.length < 2) throw new Error('At least 2 connected players are required.');
    room.winnerPlayerIds = []; room.winnerTeam = null; room.plannedRounds = getPlannedRounds(active.length); room.round = 1; room.roundSeed = Math.floor(Math.random() * 2_147_483_000);
    for (const p of room.players.values()) { if (p.disconnectTimer) clearTimeout(p.disconnectTimer); p.status = p.connected ? 'connected' : 'eliminated'; p.submitted = false; p.score = null; }
    this.assignTeams(room); this.beginMemorize(room);
  }

  returnToLobby(playerId) {
    const room = this.roomForPlayer(playerId);
    if (!room || room.phase !== 'game-over') return;
    room.phase='lobby'; room.round=0; room.phaseEndsAt=null; room.winnerPlayerIds=[]; room.winnerTeam=null;
    for (const p of room.players.values()) { if (p.disconnectTimer) clearTimeout(p.disconnectTimer); p.status=p.connected?'connected':'reconnecting'; p.submitted=false; p.score=null; p.carved=Array(27).fill(0); }
    this.assignTeams(room); this.emitRoom(room);
  }

  carveCell(playerId, index) {
    const room = this.roomForPlayer(playerId); if (!room || room.phase !== 'carve') return;
    const p = room.players.get(playerId); if (!p || p.status !== 'connected' || p.submitted) return;
    if (Date.now() >= room.phaseEndsAt) return this.eliminateForTimeout(room, p);
    if (!Number.isInteger(index) || index < 0 || index >= 27) return;
    p.carved[index] = 1;
    this.sendTo(p.connection, 'game:player-state', { carved: [...p.carved] });
    this.sendTo(p.connection, 'game:player-update', { playerId, score: scorePattern(p.carved, room.target), submitted: false, status: p.status });
  }

  resetCarve(playerId) {
    const room = this.roomForPlayer(playerId); if (!room || room.phase !== 'carve') return;
    const p = room.players.get(playerId); if (!p || p.status !== 'connected' || p.submitted) return;
    if (Date.now() >= room.phaseEndsAt) return this.eliminateForTimeout(room, p);
    p.carved = Array(27).fill(0); p.score = scorePattern(p.carved, room.target);
    this.sendTo(p.connection, 'game:player-state', { carved: [...p.carved] });
    this.sendTo(p.connection, 'game:player-update', { playerId, score: p.score, submitted:false, status:p.status });
  }

  submit(playerId) {
    const room = this.roomForPlayer(playerId); if (!room || room.phase !== 'carve') return;
    const p = room.players.get(playerId); if (!p || p.status !== 'connected' || p.submitted) return;
    // Critical rule: server time is the authority. Submit at/after timeout is always an elimination.
    if (Date.now() >= room.phaseEndsAt) return this.eliminateForTimeout(room, p);
    p.score = scorePattern(p.carved, room.target); p.submitted = true;
    if (p.score < getRequiredScore(room.players.size)) p.status = 'eliminated';
    this.broadcastPlayerUpdate(room, p); this.maybeFinishCarve(room, false);
  }

  disconnect(playerId, connection) {
    const room = this.roomForPlayer(playerId); if (!room) return;
    const p = room.players.get(playerId); if (!p || p.connection !== connection) return;
    p.connected=false; p.connection=null;
    if (room.phase === 'lobby') {
      room.players.delete(playerId); this.playerRoom.delete(playerId);
      if (room.hostId === playerId) room.hostId = [...room.players.values()][0]?.id ?? '';
      if (room.players.size === 0) this.rooms.delete(room.code); else { this.assignTeams(room); this.emitRoom(room); }
      return;
    }
    p.status='reconnecting'; this.broadcastPlayerUpdate(room,p);
    p.disconnectTimer=setTimeout(()=>{
      const current=room.players.get(playerId); if (!current || current.connected || current.status==='eliminated') return;
      current.status='eliminated'; this.broadcastPlayerUpdate(room,current); this.maybeFinishCarve(room,true);
    }, GAME_CONFIG.RECONNECT_GRACE_MS);
  }

  leaveRoom(playerId) {
    const room=this.roomForPlayer(playerId); if (!room) return; const p=room.players.get(playerId); if (!p) return;
    if (p.disconnectTimer) clearTimeout(p.disconnectTimer);
    room.players.delete(playerId); this.playerRoom.delete(playerId);
    if (room.hostId===playerId) room.hostId=[...room.players.values()][0]?.id ?? '';
    if (room.players.size===0) { this.rooms.delete(room.code); return; }
    if (room.phase==='carve') this.maybeFinishCarve(room,true);
    if (room.phase==='lobby' || room.phase==='game-over' || room.phase==='round-result') { this.assignTeams(room); this.emitRoom(room); }
  }

  tick() {
    for (const room of this.rooms.values()) {
      if (room.phase==='memorize' && Date.now()>=room.phaseEndsAt) this.beginCarve(room);
      if (room.phase==='carve' && Date.now()>=room.phaseEndsAt) {
        for (const p of room.players.values()) if (p.status==='connected' && !p.submitted) this.eliminateForTimeout(room,p);
        this.maybeFinishCarve(room,true);
      }
    }
  }

  beginMemorize(room) {
    room.phase='memorize'; room.target=generatePattern(room.roundSeed + room.round*7919); room.phaseEndsAt=Date.now()+GAME_CONFIG.MEMORIZE_SECONDS*1000;
    for (const p of room.players.values()) if (p.status!=='eliminated') { p.carved=Array(27).fill(0); p.submitted=false; p.score=null; p.status=p.connected?'connected':'reconnecting'; }
    this.emitRoom(room); this.broadcastToRoom(room,'game:memorize',{round:room.round,pattern:room.target,durationMs:GAME_CONFIG.MEMORIZE_SECONDS*1000,endsAt:room.phaseEndsAt});
  }

  beginCarve(room) {
    if (room.phase!=='memorize') return;
    room.phase='carve'; room.phaseEndsAt=Date.now()+getCarveSeconds(room.players.size)*1000;
    for (const p of room.players.values()) if (p.status!=='eliminated') { p.carved=Array(27).fill(0); p.submitted=false; p.score=scorePattern(p.carved,room.target); }
    this.emitRoom(room); this.broadcastToRoom(room,'game:carve',{round:room.round,endsAt:room.phaseEndsAt,requiredScore:getRequiredScore(room.players.size)});
  }

  eliminateForTimeout(room,p) { if (p.status==='eliminated') return; p.status='eliminated'; p.submitted=false; p.score=scorePattern(p.carved,room.target); this.broadcastPlayerUpdate(room,p); }

  maybeFinishCarve(room,timedOut) {
    if (room.phase!=='carve') return;
    const active=[...room.players.values()].filter(p=>p.status!=='eliminated');
    const activeTeams=new Set(active.map(p=>p.team).filter(Boolean));
    const gameHasWinner=room.mode==='teams' ? activeTeams.size<=1 : active.length<=1;
    if (gameHasWinner) return this.finishGame(room,this.winnerIds(room,active));
    if (!timedOut) {
      if (active.some(p=>!p.submitted && p.connected)) return;
      if (active.some(p=>p.status==='reconnecting')) return;
    }
    const results={}; const eliminated=[];
    for (const p of active) {
      const s=scorePattern(p.carved,room.target); results[p.id]=s;
      if (!p.submitted || s<getRequiredScore(room.players.size)) { p.status='eliminated'; eliminated.push(p.id); }
    }
    const remaining=[...room.players.values()].filter(p=>p.status!=='eliminated');
    const remainingTeams=new Set(remaining.map(p=>p.team).filter(Boolean));
    const teamWinner=room.mode==='teams' && remainingTeams.size<=1;
    room.phase='round-result'; room.phaseEndsAt=Date.now()+GAME_CONFIG.RESULT_MS;
    this.broadcastToRoom(room,'game:round-result',{round:room.round,eliminated,scores:results,durationMs:GAME_CONFIG.RESULT_MS}); this.emitRoom(room);
    if (remaining.length<=1 || teamWinner) {
      const ids=room.mode==='teams' && remaining[0]?.team ? remaining.filter(p=>p.team===remaining[0].team).map(p=>p.id) : remaining.map(p=>p.id);
      setTimeout(()=>this.finishGame(room,ids),GAME_CONFIG.RESULT_MS); return;
    }
    setTimeout(()=>this.advanceRound(room),GAME_CONFIG.RESULT_MS);
  }

  advanceRound(room) {
    if (!this.rooms.has(room.code) || room.phase!=='round-result') return;
    const active=[...room.players.values()].filter(p=>p.status!=='eliminated');
    const teams=new Set(active.map(p=>p.team).filter(Boolean));
    if ((room.mode==='teams' ? teams.size<=1 : active.length<=1)) return this.finishGame(room,this.winnerIds(room,active));
    room.round++; room.roundSeed+=101; this.beginMemorize(room);
  }

  winnerIds(room,active) {
    if (room.mode==='teams' && active[0]?.team) return active.filter(p=>p.team===active[0].team).map(p=>p.id);
    return active.map(p=>p.id);
  }

  finishGame(room,winnerIds) {
    if (!this.rooms.has(room.code)) return;
    room.phase='game-over'; room.phaseEndsAt=null; room.winnerPlayerIds=winnerIds;
    for (const p of room.players.values()) if (winnerIds.includes(p.id)) p.status='winner';
    room.winnerTeam=room.mode==='teams' && winnerIds[0] ? room.players.get(winnerIds[0])?.team ?? null : null;
    this.emitRoom(room); this.broadcastToRoom(room,'game:over',{mode:room.mode,winnerPlayerIds:winnerIds,winnerTeam:room.winnerTeam});
  }

  assignTeams(room) { if (room.mode==='ffa') for (const p of room.players.values()) p.team=null; else [...room.players.values()].sort((a,b)=>a.id.localeCompare(b.id)).forEach((p,i)=>p.team=i%2===0?'A':'B'); }
  emitRoom(room) { this.broadcastToRoom(room,'room:state',this.serialize(room)); }
  serialize(room) { return {code:room.code,hostId:room.hostId,mode:room.mode,phase:room.phase,round:room.round,plannedRounds:room.plannedRounds,phaseEndsAt:room.phaseEndsAt,winnerPlayerIds:room.winnerPlayerIds,winnerTeam:room.winnerTeam,players:[...room.players.values()].map(p=>({id:p.id,name:p.name,connected:p.connected,status:p.status,team:p.team}))}; }
  broadcastPlayerUpdate(room,p) { this.broadcastToRoom(room,'game:player-update',{playerId:p.id,score:p.score,submitted:p.submitted,status:p.status}); this.emitRoom(room); }
  roomForPlayer(id) { const code=this.playerRoom.get(id); return code ? this.rooms.get(code) ?? null : null; }
  makePlayer(name,connection) { return {id:crypto.randomUUID(),name:sanitizeName(name),connection,connected:true,status:'connected',team:null,carved:Array(27).fill(0),submitted:false,score:null,disconnectTimer:null}; }
  makeRoomCode() { const alphabet='ABCDEFGHJKLMNPQRSTUVWXYZ23456789'; for(let a=0;a<100;a++){let code='';for(let i=0;i<5;i++)code+=alphabet[Math.floor(Math.random()*alphabet.length)];if(!this.rooms.has(code))return code;} throw new Error('Could not allocate room code.'); }
}



const __dirname=path.dirname(fileURLToPath(import.meta.url));
const publicDir=path.resolve(__dirname,'../public');
const clients=new Set();

function sendTo(connection,event,data){connection?.send(event,data);}
function broadcastToRoom(room,event,data){for(const p of room.players.values()) if(p.connection && p.connected) p.connection.send(event,data);}
const game=new GameManager(sendTo,broadcastToRoom);

const mime={'.html':'text/html; charset=utf-8','.js':'text/javascript; charset=utf-8','.css':'text/css; charset=utf-8','.webmanifest':'application/manifest+json','.png':'image/png','.svg':'image/svg+xml','.ico':'image/x-icon'};

const server=http.createServer((req,res)=>{
  if(req.url==='/health'){res.writeHead(200,{'content-type':'application/json'});res.end(JSON.stringify({ok:true,service:'carve-survival'}));return;}
  const url=new URL(req.url,'http://localhost');
  let filePath=path.join(publicDir,url.pathname==='/'?'index.html':url.pathname);
  if(!filePath.startsWith(publicDir)) {res.writeHead(403);res.end();return;}
  if(!fs.existsSync(filePath) || fs.statSync(filePath).isDirectory()) filePath=path.join(publicDir,'index.html');
  const ext=path.extname(filePath);
  res.writeHead(200,{'content-type':mime[ext]||'application/octet-stream','cache-control':url.pathname==='/'?'no-cache':'public, max-age=31536000, immutable'});
  fs.createReadStream(filePath).pipe(res);
});

server.on('upgrade',(req,socket)=>{
  const ws=upgradeToWebSocket(req,socket); if(!ws) return;
  clients.add(ws);
  ws.on('message',(msg)=>{
    if(!msg || msg.type!=='request') return;
    const {id,event,data}=msg;
    try {
      let result={ok:true};
      switch(event){
        case 'room:create': result.playerId=game.createRoom(ws,data?.name,data?.mode); break;
        case 'room:join': result.playerId=game.joinRoom(ws,data?.code,data?.name); break;
        case 'session:reconnect': game.reconnect(ws,data?.playerId); break;
        case 'room:mode': game.updateMode(data?.playerId,data?.mode); break;
        case 'room:start': game.startRoom(data?.playerId); break;
        case 'room:play-again': game.playAgain(data?.playerId); break;
        case 'room:return-lobby': game.returnToLobby(data?.playerId); break;
        case 'player:name': game.updateName(data?.playerId,data?.name); break;
        case 'game:carve': game.carveCell(data?.playerId,data?.index); break;
        case 'game:reset': game.resetCarve(data?.playerId); break;
        case 'game:submit': game.submit(data?.playerId); break;
        case 'room:leave': game.leaveRoom(data?.playerId); break;
        default: throw new Error('Unknown event.');
      }
      ws.ack(id,result);
    } catch(error){ ws.ack(id,{ok:false,message:error instanceof Error?error.message:'Request failed.'}); }
  });
  ws.on('disconnect',()=>{clients.delete(ws); for(const [playerId] of game.playerRoom){game.disconnect(playerId,ws);} });
});

setInterval(()=>game.tick(),100);
const port=Number(process.env.PORT||3000);
server.listen(port,'0.0.0.0',()=>console.log(`Carve Survival listening on http://localhost:${port}`));
