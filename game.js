'use strict';

(() => {
  // ---------- Constants ----------
  const COLS = 10;
  const ROWS = 20;
  const BUFFER = 2;               // hidden rows above the visible field
  const TOTAL = ROWS + BUFFER;
  const LOCK_DELAY = 500;         // ms a grounded piece waits before locking
  const MAX_LOCK_RESETS = 15;
  const CLEAR_ANIM = 180;         // ms line-clear flash
  const DAS = 170;                // delayed auto shift (ms)
  const ARR = 45;                 // auto repeat rate (ms)
  const SOFT_DROP_INTERVAL = 35;  // ms per row while soft dropping
  const LINE_SCORES = [0, 100, 300, 500, 800];

  const COLORS = {
    I: '#2ee6e6', J: '#3b6cff', L: '#ff9a1f', O: '#ffd60a',
    S: '#3ddc57', T: '#b45cff', Z: '#ff4757',
  };

  const SHAPES = {
    I: [[0,0,0,0],[1,1,1,1],[0,0,0,0],[0,0,0,0]],
    J: [[1,0,0],[1,1,1],[0,0,0]],
    L: [[0,0,1],[1,1,1],[0,0,0]],
    O: [[1,1],[1,1]],
    S: [[0,1,1],[1,1,0],[0,0,0]],
    T: [[0,1,0],[1,1,1],[0,0,0]],
    Z: [[1,1,0],[0,1,1],[0,0,0]],
  };

  // Precompute the 4 rotation states of each piece as lists of [x, y] cells.
  const rotateCW = m => m.map((row, y) => row.map((_, x) => m[m.length - 1 - x][y]));
  const toCells = m => m.flatMap((row, y) => row.flatMap((v, x) => (v ? [[x, y]] : [])));
  const ROT = {};
  for (const [type, shape] of Object.entries(SHAPES)) {
    const states = [shape];
    for (let i = 1; i < 4; i++) states.push(rotateCW(states[i - 1]));
    ROT[type] = states.map(toCells);
  }

  // SRS wall kicks (y is up in the spec; negated when applied since our y points down).
  const KICKS = {
    '0>1': [[0,0],[-1,0],[-1,1],[0,-2],[-1,-2]],
    '1>0': [[0,0],[1,0],[1,-1],[0,2],[1,2]],
    '1>2': [[0,0],[1,0],[1,-1],[0,2],[1,2]],
    '2>1': [[0,0],[-1,0],[-1,1],[0,-2],[-1,-2]],
    '2>3': [[0,0],[1,0],[1,1],[0,-2],[1,-2]],
    '3>2': [[0,0],[-1,0],[-1,-1],[0,2],[-1,2]],
    '3>0': [[0,0],[-1,0],[-1,-1],[0,2],[-1,2]],
    '0>3': [[0,0],[1,0],[1,1],[0,-2],[1,-2]],
  };
  const KICKS_I = {
    '0>1': [[0,0],[-2,0],[1,0],[-2,-1],[1,2]],
    '1>0': [[0,0],[2,0],[-1,0],[2,1],[-1,-2]],
    '1>2': [[0,0],[-1,0],[2,0],[-1,2],[2,-1]],
    '2>1': [[0,0],[1,0],[-2,0],[1,-2],[-2,1]],
    '2>3': [[0,0],[2,0],[-1,0],[2,1],[-1,-2]],
    '3>2': [[0,0],[-2,0],[1,0],[-2,-1],[1,2]],
    '3>0': [[0,0],[1,0],[-2,0],[1,-2],[-2,1]],
    '0>3': [[0,0],[-1,0],[2,0],[-1,2],[2,-1]],
  };

  // ---------- DOM ----------
  const $ = id => document.getElementById(id);
  const boardCanvas = $('board'), bctx = boardCanvas.getContext('2d');
  const holdCanvas = $('hold'), hctx = holdCanvas.getContext('2d');
  const nextCanvas = $('next'), nctx = nextCanvas.getContext('2d');
  const boardWrap = $('boardWrap');
  const overlay = $('overlay'), ovTitle = $('ovTitle'), ovText = $('ovText'), ovBtn = $('ovBtn');
  const scoreEl = $('score'), levelEl = $('level'), linesEl = $('lines'), pauseBtn = $('pauseBtn');
  const settingsSheet = $('settings'), settingsBtn = $('settingsBtn');
  const moveSensEl = $('moveSens'), dropSensEl = $('dropSens'), axisLockEl = $('axisLock');

  // ---------- Storage ----------
  const store = {
    get(k, d) { try { const v = localStorage.getItem(k); return v === null ? d : JSON.parse(v); } catch { return d; } },
    set(k, v) { try { localStorage.setItem(k, JSON.stringify(v)); } catch {} },
  };
  let highScore = store.get('blocks.high', 0);

  // ---------- Settings ----------
  const DEFAULT_SETTINGS = { moveSens: 4, dropSens: 4, axisLock: true };
  let settings = { ...DEFAULT_SETTINGS, ...store.get('blocks.settings', {}) };
  // Cells of finger travel needed to move one column (sens 1 → 1.8 cells, sens 10 → 0.54).
  const dragPerColumn = () => 1.8 - (settings.moveSens - 1) * 0.14;
  // Finger speed (px/ms) a downward flick needs to hard drop (sens 1 → 2.2, sens 10 → 0.6).
  const flickSpeed = () => 2.2 - (settings.dropSens - 1) * 0.178;

  // ---------- Game state ----------
  let board, cur, queue, bag, holdType, canHold;
  let score, lines, level;
  let state = 'menu'; // menu | playing | paused | over
  let dropAcc, lockTimer, lockResets, lowestY;
  let softDrop = false;
  let clearRows = null, clearTimer = 0;

  const emptyRow = () => new Array(COLS).fill(null);

  function newGame() {
    board = Array.from({ length: TOTAL }, emptyRow);
    bag = [];
    queue = [];
    while (queue.length < 5) queue.push(nextFromBag());
    holdType = null;
    canHold = true;
    score = 0; lines = 0; level = 1;
    clearRows = null;
    softDrop = false;
    spawn(queue.shift());
    state = 'playing';
    hideOverlay();
    updateStats();
    drawSide();
  }

  function nextFromBag() {
    if (!bag.length) {
      bag = Object.keys(SHAPES);
      for (let i = bag.length - 1; i > 0; i--) {
        const j = Math.floor(Math.random() * (i + 1));
        [bag[i], bag[j]] = [bag[j], bag[i]];
      }
    }
    return bag.pop();
  }

  function spawn(type) {
    cur = { type, rot: 0, x: type === 'O' ? 4 : 3, y: BUFFER - 1 };
    dropAcc = 0; lockTimer = 0; lockResets = 0; lowestY = cur.y;
    if (collides(cur)) {
      cur.y--;                       // try one row higher before topping out
      if (collides(cur)) return gameOver();
    }
    while (queue.length < 5) queue.push(nextFromBag());
    drawSide();
  }

  const cellsOf = p => ROT[p.type][p.rot].map(([x, y]) => [p.x + x, p.y + y]);

  function collides(p) {
    for (const [x, y] of cellsOf(p)) {
      if (x < 0 || x >= COLS || y >= TOTAL) return true;
      if (y >= 0 && board[y][x]) return true;
    }
    return false;
  }

  const grounded = () => collides({ ...cur, y: cur.y + 1 });

  function onSuccessfulMove() {
    if (cur.y > lowestY) { lowestY = cur.y; lockResets = 0; }
    if (grounded() && lockResets < MAX_LOCK_RESETS) { lockTimer = 0; lockResets++; }
  }

  function move(dx, dy) {
    const p = { ...cur, x: cur.x + dx, y: cur.y + dy };
    if (collides(p)) return false;
    cur = p;
    onSuccessfulMove();
    return true;
  }

  function rotate(dir) {
    if (cur.type === 'O') return;
    const from = cur.rot, to = (from + dir + 4) % 4;
    const kicks = (cur.type === 'I' ? KICKS_I : KICKS)[`${from}>${to}`];
    for (const [kx, ky] of kicks) {
      const p = { ...cur, rot: to, x: cur.x + kx, y: cur.y - ky };
      if (!collides(p)) { cur = p; onSuccessfulMove(); return; }
    }
  }

  function hardDrop() {
    let n = 0;
    while (!collides({ ...cur, y: cur.y + 1 })) { cur.y++; n++; }
    score += n * 2;
    buzz(8);
    lock();
  }

  function hold() {
    if (!canHold) return;
    const t = cur.type;
    if (holdType) spawn(holdType); else spawn(queue.shift());
    holdType = t;
    canHold = false;
    drawSide();
  }

  function lock() {
    const cells = cellsOf(cur);
    for (const [x, y] of cells) if (y >= 0) board[y][x] = cur.type;
    if (cells.every(([, y]) => y < BUFFER)) return gameOver(); // locked entirely above the field

    const full = [];
    for (let y = 0; y < TOTAL; y++) if (board[y].every(Boolean)) full.push(y);
    canHold = true;
    if (full.length) {
      clearRows = full;
      clearTimer = CLEAR_ANIM;
      cur = null;
      buzz(full.length === 4 ? [20, 40, 20] : 20);
    } else {
      spawn(queue.shift());
    }
    updateStats();
  }

  function finishClear() {
    const n = clearRows.length;
    board = board.filter((_, y) => !clearRows.includes(y));
    while (board.length < TOTAL) board.unshift(emptyRow());
    clearRows = null;
    score += LINE_SCORES[n] * level;
    lines += n;
    level = Math.floor(lines / 10) + 1;
    updateStats();
    spawn(queue.shift());
  }

  function gravityInterval() {
    // Guideline gravity curve: seconds per row.
    const lv = Math.min(level, 20) - 1;
    return Math.pow(0.8 - lv * 0.007, lv) * 1000;
  }

  function update(dt) {
    if (state !== 'playing') return;
    if (clearRows) {
      clearTimer -= dt;
      if (clearTimer <= 0) finishClear();
      return;
    }
    if (!cur) return;

    const gravity = gravityInterval();
    const interval = softDrop ? Math.min(gravity, SOFT_DROP_INTERVAL) : gravity;
    if (!grounded()) {
      lockTimer = 0;
      dropAcc += dt;
      while (dropAcc >= interval) {
        dropAcc -= interval;
        if (!move(0, 1)) break;
        if (softDrop) score += 1;
      }
    } else {
      dropAcc = 0;
      lockTimer += dt;
      if (lockTimer >= LOCK_DELAY) lock();
    }
    updateStats();
  }

  function gameOver() {
    state = 'over';
    cur = null;
    stopAllRepeats();
    const isNew = score > highScore;
    if (isNew) { highScore = score; store.set('blocks.high', highScore); }
    showOverlay('GAME OVER',
      `<span class="big">${score.toLocaleString()}</span><br>${isNew ? 'New high score!' : `Best: ${highScore.toLocaleString()}`}`,
      'PLAY AGAIN');
  }

  function pause() {
    if (state !== 'playing') return;
    state = 'paused';
    stopAllRepeats();
    showOverlay('PAUSED', `Best: ${highScore.toLocaleString()}`, 'RESUME');
  }

  function resume() {
    if (state !== 'paused') return;
    state = 'playing';
    hideOverlay();
  }

  // ---------- UI ----------
  function showOverlay(title, html, btn) {
    ovTitle.textContent = title;
    ovText.innerHTML = html;
    ovBtn.textContent = btn;
    overlay.classList.remove('hidden');
    pauseBtn.textContent = 'PAUSE';
  }
  function hideOverlay() { overlay.classList.add('hidden'); }

  let lastStats = '';
  function updateStats() {
    const s = `${score}|${level}|${lines}`;
    if (s === lastStats) return;
    lastStats = s;
    scoreEl.textContent = score.toLocaleString();
    levelEl.textContent = level;
    linesEl.textContent = lines;
  }

  function buzz(pattern) { try { navigator.vibrate && navigator.vibrate(pattern); } catch {} }

  ovBtn.addEventListener('click', () => {
    if (state === 'paused') resume(); else newGame();
  });
  pauseBtn.addEventListener('click', () => {
    if (state === 'playing') pause(); else if (state === 'paused') resume();
  });
  document.addEventListener('visibilitychange', () => { if (document.hidden) pause(); });

  function syncSettingsUI() {
    moveSensEl.value = settings.moveSens;
    dropSensEl.value = settings.dropSens;
    axisLockEl.checked = settings.axisLock;
    $('moveSensOut').textContent = settings.moveSens;
    $('dropSensOut').textContent = settings.dropSens;
  }
  function saveSettings() {
    settings.moveSens = +moveSensEl.value;
    settings.dropSens = +dropSensEl.value;
    settings.axisLock = axisLockEl.checked;
    store.set('blocks.settings', settings);
    syncSettingsUI();
  }
  function openSettings() {
    pause();
    syncSettingsUI();
    overlay.classList.add('hidden');
    settingsSheet.classList.remove('hidden');
  }
  function closeSettings() {
    settingsSheet.classList.add('hidden');
    overlay.classList.remove('hidden'); // back to the menu / pause / game-over screen
  }
  [moveSensEl, dropSensEl, axisLockEl].forEach(el => el.addEventListener('input', saveSettings));
  settingsBtn.addEventListener('click', () => {
    if (settingsSheet.classList.contains('hidden')) openSettings(); else closeSettings();
  });
  $('settingsDone').addEventListener('click', closeSettings);
  $('settingsReset').addEventListener('click', () => {
    settings = { ...DEFAULT_SETTINGS };
    store.set('blocks.settings', settings);
    syncSettingsUI();
  });

  // ---------- Rendering ----------
  let cell = 24;
  const dpr = () => window.devicePixelRatio || 1;

  function sizeCanvas(canvas, ctx, w, h) {
    const r = dpr();
    canvas.style.width = w + 'px';
    canvas.style.height = h + 'px';
    canvas.width = Math.round(w * r);
    canvas.height = Math.round(h * r);
    ctx.setTransform(r, 0, 0, r, 0, 0);
  }

  function resize() {
    const w = boardWrap.clientWidth, h = boardWrap.clientHeight;
    cell = Math.max(8, Math.floor(Math.min(w / COLS, h / ROWS)));
    sizeCanvas(boardCanvas, bctx, cell * COLS, cell * ROWS);
    for (const sheet of [overlay, settingsSheet]) {
      sheet.style.width = cell * COLS + 'px';
      sheet.style.height = cell * ROWS + 'px';
    }
    sizeCanvas(holdCanvas, hctx, holdCanvas.clientWidth || 60, holdCanvas.clientHeight || 40);
    sizeCanvas(nextCanvas, nctx, nextCanvas.clientWidth || 60, nextCanvas.clientHeight || 112);
    drawSide();
  }

  function shade(hex, amt) {
    const n = parseInt(hex.slice(1), 16);
    const f = c => Math.max(0, Math.min(255, Math.round(c + (amt > 0 ? (255 - c) : c) * amt)));
    return `rgb(${f(n >> 16)},${f((n >> 8) & 255)},${f(n & 255)})`;
  }

  function drawBlock(ctx, x, y, s, color, alpha = 1) {
    ctx.globalAlpha = alpha;
    const b = Math.max(1, Math.round(s * 0.12));
    ctx.fillStyle = color;
    ctx.fillRect(x, y, s, s);
    ctx.fillStyle = shade(color, 0.35);
    ctx.fillRect(x, y, s, b);
    ctx.fillRect(x, y, b, s);
    ctx.fillStyle = shade(color, -0.3);
    ctx.fillRect(x, y + s - b, s, b);
    ctx.fillRect(x + s - b, y, b, s);
    ctx.globalAlpha = 1;
  }

  function drawBoard() {
    const ctx = bctx, W = cell * COLS, H = cell * ROWS;
    ctx.fillStyle = '#0b0c19';
    ctx.fillRect(0, 0, W, H);

    ctx.strokeStyle = 'rgba(255,255,255,0.05)';
    ctx.lineWidth = 1;
    ctx.beginPath();
    for (let x = 1; x < COLS; x++) { ctx.moveTo(x * cell + 0.5, 0); ctx.lineTo(x * cell + 0.5, H); }
    for (let y = 1; y < ROWS; y++) { ctx.moveTo(0, y * cell + 0.5); ctx.lineTo(W, y * cell + 0.5); }
    ctx.stroke();

    if (!board) return;
    const flash = clearRows ? clearTimer / CLEAR_ANIM : 0;
    for (let y = BUFFER; y < TOTAL; y++) {
      const clearing = clearRows && clearRows.includes(y);
      for (let x = 0; x < COLS; x++) {
        const t = board[y][x];
        if (!t) continue;
        drawBlock(ctx, x * cell, (y - BUFFER) * cell, cell, clearing ? '#ffffff' : COLORS[t], clearing ? flash : 1);
      }
    }

    if (cur && state !== 'over') {
      let gy = cur.y;
      while (!collides({ ...cur, y: gy + 1 })) gy++;
      const color = COLORS[cur.type];
      for (const [x, y] of cellsOf({ ...cur, y: gy })) {
        if (y < BUFFER) continue;
        ctx.strokeStyle = color;
        ctx.globalAlpha = 0.5;
        ctx.lineWidth = 2;
        ctx.strokeRect(x * cell + 2, (y - BUFFER) * cell + 2, cell - 4, cell - 4);
        ctx.globalAlpha = 1;
      }
      for (const [x, y] of cellsOf(cur)) {
        if (y < BUFFER) continue;
        drawBlock(ctx, x * cell, (y - BUFFER) * cell, cell, color);
      }
    }
  }

  function drawMini(ctx, type, cx, cy, s, alpha = 1) {
    const cells = ROT[type][0];
    const xs = cells.map(c => c[0]), ys = cells.map(c => c[1]);
    const minX = Math.min(...xs), maxX = Math.max(...xs), minY = Math.min(...ys), maxY = Math.max(...ys);
    const ox = cx - ((maxX - minX + 1) * s) / 2, oy = cy - ((maxY - minY + 1) * s) / 2;
    for (const [x, y] of cells) drawBlock(ctx, ox + (x - minX) * s, oy + (y - minY) * s, s, COLORS[type], alpha);
  }

  function drawSide() {
    const hw = parseFloat(holdCanvas.style.width) || 60, hh = parseFloat(holdCanvas.style.height) || 40;
    hctx.clearRect(0, 0, hw, hh);
    if (holdType) drawMini(hctx, holdType, hw / 2, hh / 2, 12, canHold ? 1 : 0.35);

    const nw = parseFloat(nextCanvas.style.width) || 60, nh = parseFloat(nextCanvas.style.height) || 112;
    nctx.clearRect(0, 0, nw, nh);
    if (queue) queue.slice(0, 3).forEach((t, i) => drawMini(nctx, t, nw / 2, 18 + i * 38, i === 0 ? 12 : 10));
  }

  // ---------- Input: repeat helpers ----------
  const repeats = new Map();

  function act(action) {
    if (state !== 'playing' || !cur || clearRows) return;
    switch (action) {
      case 'left': move(-1, 0); break;
      case 'right': move(1, 0); break;
      case 'cw': rotate(1); break;
      case 'ccw': rotate(-1); break;
      case 'hard': hardDrop(); break;
      case 'hold': hold(); break;
    }
  }

  function startAction(action) {
    if (action === 'soft') { softDrop = true; return; }
    if (repeats.has(action)) return;
    if (action === 'left') stopAction('right');
    if (action === 'right') stopAction('left');
    act(action);
    if (action === 'left' || action === 'right') {
      const r = { timer: null };
      r.timer = setTimeout(function tick() { act(action); r.timer = setTimeout(tick, ARR); }, DAS);
      repeats.set(action, r);
    } else {
      repeats.set(action, { timer: null });
    }
  }

  function stopAction(action) {
    if (action === 'soft') { softDrop = false; return; }
    const r = repeats.get(action);
    if (r) { clearTimeout(r.timer); repeats.delete(action); }
  }

  function stopAllRepeats() {
    for (const a of [...repeats.keys()]) stopAction(a);
    softDrop = false;
  }

  // ---------- Input: keyboard ----------
  const KEYMAP = {
    ArrowLeft: 'left', ArrowRight: 'right', ArrowDown: 'soft',
    ArrowUp: 'cw', x: 'cw', X: 'cw', z: 'ccw', Z: 'ccw', Control: 'ccw',
    ' ': 'hard', c: 'hold', C: 'hold', Shift: 'hold',
  };

  window.addEventListener('keydown', e => {
    if (e.key === 'Escape' || e.key === 'p' || e.key === 'P') {
      if (state === 'playing') pause(); else if (state === 'paused') resume();
      e.preventDefault();
      return;
    }
    if (e.key === 'Enter' && state !== 'playing') { ovBtn.click(); e.preventDefault(); return; }
    const a = KEYMAP[e.key];
    if (!a) return;
    e.preventDefault();
    if (e.repeat) return;
    startAction(a);
  });
  window.addEventListener('keyup', e => {
    const a = KEYMAP[e.key];
    if (a) stopAction(a);
  });
  window.addEventListener('blur', stopAllRepeats);

  // ---------- Input: touch gestures ----------
  // Tap = rotate (left third rotates the other way), drag sideways = move, drag down = soft drop,
  // flick down = hard drop, flick up = hold. Listens on the whole play area, not just the board.
  const AXIS_COMMIT = 10; // px of travel before a swipe's direction is decided
  let gesture = null;

  boardWrap.addEventListener('pointerdown', e => {
    if (state !== 'playing' || gesture) return;
    try { boardWrap.setPointerCapture(e.pointerId); } catch {}
    const now = performance.now();
    gesture = { id: e.pointerId, x0: e.clientX, y0: e.clientY, t0: now, stepX: 0, stepY: 0,
                axis: null, moved: false, samples: [{ y: e.clientY, t: now }] };
  });

  boardWrap.addEventListener('pointermove', e => {
    const g = gesture;
    if (!g || e.pointerId !== g.id || state !== 'playing' || !cur) return;
    const dx = e.clientX - g.x0, dy = e.clientY - g.y0;
    const now = performance.now();
    g.samples.push({ y: e.clientY, t: now });
    while (g.samples.length > 2 && now - g.samples[0].t > 80) g.samples.shift();

    if (!g.moved && Math.hypot(dx, dy) > AXIS_COMMIT) {
      g.moved = true;
      g.axis = Math.abs(dx) > Math.abs(dy) ? 'x' : 'y';
    }
    if (!g.moved) return;
    const lock = settings.axisLock;

    if (!lock || g.axis === 'x') {
      const tx = Math.trunc(dx / (cell * dragPerColumn()));
      while (g.stepX < tx) { act('right'); g.stepX++; }
      while (g.stepX > tx) { act('left'); g.stepX--; }
    }
    if ((!lock || g.axis === 'y') && dy > 0) {
      const ty = Math.trunc(dy / (cell * dragPerColumn()));
      while (g.stepY < ty) { if (move(0, 1)) score += 1; g.stepY++; }
    }
  });

  function endGesture(e) {
    const g = gesture;
    if (!g || e.pointerId !== g.id) return;
    gesture = null;
    if (state !== 'playing') return;
    const dx = e.clientX - g.x0, dy = e.clientY - g.y0, dt = performance.now() - g.t0;
    const first = g.samples[0]; // finger speed over roughly the last 80ms
    const vy = (e.clientY - first.y) / Math.max(1, performance.now() - first.t);
    const vertical = settings.axisLock ? g.axis === 'y' : Math.abs(dy) > Math.abs(dx);

    if (!g.moved && dt < 300) {
      const rect = boardCanvas.getBoundingClientRect();
      act(e.clientX - rect.left < rect.width / 3 ? 'ccw' : 'cw');
    } else if (vertical && dy > cell * 1.5 && vy > flickSpeed()) {
      act('hard');
    } else if (vertical && dy < -cell * 2 && dt < 400) {
      act('hold');
    }
  }
  boardWrap.addEventListener('pointerup', endGesture);
  boardWrap.addEventListener('pointercancel', e => { if (gesture && e.pointerId === gesture.id) gesture = null; });

  // ---------- Main loop ----------
  let last = performance.now();
  function frame(now) {
    const dt = Math.min(100, now - last);
    last = now;
    update(dt);
    drawBoard();
    requestAnimationFrame(frame);
  }

  window.addEventListener('resize', resize);
  new ResizeObserver(resize).observe(boardWrap);
  resize();
  showOverlay('BLOCKS',
    `Best: ${highScore.toLocaleString()}<br><br>` +
    (matchMedia('(pointer: fine)').matches
      ? '← → move · ↓ soft drop · Space hard drop<br>↑/X rotate · Z rotate left · C hold · P pause'
      : 'Tap board to rotate · drag to move<br>Flick down to drop · flick up to hold'),
    'PLAY');
  requestAnimationFrame(frame);
})();
