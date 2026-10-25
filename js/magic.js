"use strict";
/* ================= magic squares: the closed forms =================
   Every construction has a closed form, so a cell's value is computed from (i, j)
   on demand and nothing is ever stored. Memory is O(1) at any order, and drawing
   costs only the cells you can actually see. These functions are also serialised
   into the verification worker and the HTML export, so keep them self-contained. */
const LUX_PAT = { L:[[4,1],[2,3]], U:[[1,4],[2,3]], X:[[1,4],[3,2]] };
function siameseCell(n, i, j){
  return n * ((i + j + 1 + (n >> 1)) % n) + ((i + 2*j + 1) % n) + 1;
}
function doublyEvenCell(n, i, j){
  const v = i*n + j + 1, a = i % 4, b = j % 4;
  return (a === b || a + b === 3) ? n*n + 1 - v : v;
}
function luxCell(n, i, j){
  const half = n / 2, mm = (n - 2) / 4, a = i >> 1, b = j >> 1;
  let t = a <= mm ? "L" : a === mm + 1 ? "U" : "X";
  if (a === mm && b === mm) t = "U";
  else if (a === mm + 1 && b === mm) t = "L";
  return 4 * (siameseCell(half, a, b) - 1) + LUX_PAT[t][i & 1][j & 1];
}
/** The value in row i, column j (both 0-based) of the order-n square. O(1). */
function cellAt(n, i, j){
  if (n % 2) return siameseCell(n, i, j);
  return n % 4 === 0 ? doublyEvenCell(n, i, j) : luxCell(n, i, j);
}
/** The same cell after a symmetry t = {swap, fi, fj} and an optional complement. */
function symCell(n, t, comp, i, j){
  let a = t.swap ? j : i, b = t.swap ? i : j;
  if (t.fi) a = n - 1 - a;
  if (t.fj) b = n - 1 - b;
  const v = cellAt(n, a, b);
  return comp ? n*n + 1 - v : v;
}
/* Past n ≈ 94.9 million, n² outgrows the integers a double holds exactly, so the
   same closed forms are repeated in BigInt for the values that are shown as text.
   Colours can stay approximate; numbers cannot. Takes Number indices, returns a BigInt. */
function symCellBig(n, t, comp, i, j){
  let a = t.swap ? j : i, b = t.swap ? i : j;
  if (t.fi) a = n - 1 - a;
  if (t.fj) b = n - 1 - b;
  const N = BigInt(n), I = BigInt(a), J = BigInt(b);
  const siam = (m, x, y) => m * ((x + y + 1n + m / 2n) % m) + ((x + 2n * y + 1n) % m) + 1n;
  let v;
  if (N % 2n) v = siam(N, I, J);
  else if (N % 4n === 0n){
    const lin = I * N + J + 1n, p = I % 4n, q = J % 4n;
    v = (p === q || p + q === 3n) ? N * N + 1n - lin : lin;
  } else {
    const mm = (N - 2n) / 4n, A = I / 2n, B = J / 2n;
    let k = A <= mm ? "L" : A === mm + 1n ? "U" : "X";
    if (A === mm && B === mm) k = "U";
    else if (A === mm + 1n && B === mm) k = "L";
    v = 4n * (siam(N / 2n, A, B) - 1n) + BigInt(LUX_PAT[k][a & 1][b & 1]);
  }
  return comp ? N * N + 1n - v : v;
}
const EXACT_ORDER = 94906265;          // largest n with n² ≤ 2^53
const MSQ_KERNEL = "const LUX_PAT = " + JSON.stringify(LUX_PAT) + ";\n"
  + [siameseCell, doublyEvenCell, luxCell, cellAt, symCell, symCellBig].map(String).join("\n");

/* The eight symmetries of the square are every combination of a transpose and two
   flips. Rotating or mirroring composes a new one; which one is found by probing a
   3 × 3 grid, which is enough to tell all eight apart. */
const SYMS = [];
for (const swap of [0, 1]) for (const fi of [0, 1]) for (const fj of [0, 1]) SYMS.push({ swap, fi, fj });
function symMap(t, n, i, j){
  let a = t.swap ? j : i, b = t.swap ? i : j;
  if (t.fi) a = n - 1 - a;
  if (t.fj) b = n - 1 - b;
  return [a, b];
}
function symCompose(k, op){
  const t = SYMS[k];
  for (let c = 0; c < 8; c++){
    let same = true;
    for (let i = 0; i < 3 && same; i++) for (let j = 0; j < 3 && same; j++){
      const [pi, pj] = op(3, i, j);
      const want = symMap(t, 3, pi, pj), got = symMap(SYMS[c], 3, i, j);
      same = want[0] === got[0] && want[1] === got[1];
    }
    if (same) return c;
  }
  return k;
}
const ROTATE_CW = (n, i, j) => [n - 1 - j, i];
const MIRROR_LR = (n, i, j) => [i, n - 1 - j];

/* ================= verification worker =================
   Proving every line of a large square is 2n² additions, so it runs in the
   background with progress, spending a fixed budget of cell reads: everything is
   checked outright while that is affordable, and past it the checks are sampled and
   the result says so. Sums are on the base values 1 … n²; first number a and step d
   map every line sum S to n·a + d·(S − n), so a line is magic in one exactly when it
   is in the other. */
function msqCheckBody(){
  const FULL_BUDGET = 6e8;               // cell reads: a few seconds of background work
  /* A line of n values can sum past 2^53, so fold Number partials into a BigInt
     often enough that a partial never leaves the exact range. */
  let foldEvery = 4096;
  function lineSum(n, get){
    let total = 0n, part = 0;
    for (let k = 0; k < n; k++){
      part += get(k);
      if (k % foldEvery === foldEvery - 1){ total += BigInt(part); part = 0; }
    }
    return total + BigInt(part);
  }
  const fmt = v => v.toLocaleString("en-US");
  onmessage = e => {
    const { n, t, comp } = e.data;
    const t0 = performance.now();
    const S = BigInt(n) * (BigInt(n) * BigInt(n) + 1n) / 2n;
    let lastPost = 0;
    const post = (phase, f) => {
      const now = performance.now();
      if (now - lastPost > 80){ lastPost = now; postMessage({ type: "progress", phase, frac: f }); }
    };
    const out = { type: "done", ok: true, scope: "", assoc: null, pandiag: null };
    const finish = () => { out.ms = performance.now() - t0; postMessage(out); };

    if (n * n > 9007199254740991){
      // past exact doubles: every read is a BigInt, so prove what a few minutes allow
      const big = (get, what, base) => {
        let s = 0n;
        for (let k = 0; k < n; k++){ s += get(k); if ((k & 65535) === 0) post("summing " + what, base + k / n * 0.25); }
        return s;
      };
      const checks = [[k => symCellBig(n, t, comp, k, k), "the main diagonal"],
                      [k => symCellBig(n, t, comp, k, n - 1 - k), "the anti-diagonal"],
                      [k => symCellBig(n, t, comp, 0, k), "row 1"],
                      [k => symCellBig(n, t, comp, k, 0), "column 1"]];
      for (let c = 0; c < checks.length; c++){
        if (big(checks[c][0], checks[c][1], c * 0.25) !== S){ out.ok = false; out.scope = checks[c][1] + " is off"; return finish(); }
      }
      out.scope = "both diagonals, row 1 and column 1 ✓";
      return finish();
    }
    foldEvery = Math.max(1, Math.min(4096, Math.floor(9007199254740991 / (n * n))));
    const at = (i, j) => symCell(n, t, comp, i, j);

    if (lineSum(n, k => at(k, k)) !== S || lineSum(n, k => at(k, n - 1 - k)) !== S){
      out.ok = false; out.scope = "a diagonal is off"; return finish();
    }
    const fullLines = 2 * n * n <= FULL_BUDGET;
    const step = fullLines ? 1 : Math.max(1, Math.floor(n / Math.max(2, Math.floor(FULL_BUDGET / 6 / (2 * n)))));
    let lines = 2;
    for (let i = 0; i < n; i += step){
      if (lineSum(n, k => at(i, k)) !== S){ out.ok = false; out.scope = "row " + fmt(i + 1) + " is off"; return finish(); }
      if (lineSum(n, k => at(k, i)) !== S){ out.ok = false; out.scope = "column " + fmt(i + 1) + " is off"; return finish(); }
      lines += 2;
      post("summing rows and columns", i / n * 0.55);
    }
    if (fullLines && n * n <= 1.6e7){
      const seen = new Uint8Array(n * n + 1);
      for (let i = 0; i < n; i++){
        for (let j = 0; j < n; j++){
          const v = at(i, j);
          if (v < 1 || v > n * n || seen[v]){ out.ok = false; out.scope = "the value " + fmt(v) + " repeats"; return finish(); }
          seen[v] = 1;
        }
        post("checking every value appears once", 0.55 + i / n * 0.15);
      }
      out.scope = "every row, column and diagonal ✓ · each of " + fmt(n * n) + " values used once ✓";
    } else if (fullLines){
      out.scope = "all " + fmt(n) + " rows, all " + fmt(n) + " columns and both diagonals ✓";
    } else {
      out.scope = "both diagonals and " + fmt(lines - 2) + " evenly spaced rows and columns ✓ (all "
        + fmt(2 * n) + " lines would be " + fmt(2 * n * n) + " additions)";
    }

    // associative: every pair of cells symmetric about the centre adds to n² + 1
    const pairBudget = FULL_BUDGET / 2;
    const assocStep = n * n <= pairBudget ? 1 : Math.max(1, Math.floor(n * n / pairBudget));
    let assoc = true;
    outer: for (let i = 0; i < n; i += assocStep){
      for (let j = 0; j < n; j++){
        if (at(i, j) + at(n - 1 - i, n - 1 - j) !== n * n + 1){ assoc = false; break outer; }
      }
      post("testing symmetry about the centre", 0.7 + i / n * 0.1);
    }
    out.assoc = { yes: assoc, sampled: assocStep > 1 };

    // pandiagonal: every broken diagonal, in both directions, is magic too
    const pdStep = 2 * n * n <= FULL_BUDGET ? 1 : Math.max(1, Math.floor(2 * n * n / FULL_BUDGET));
    let pd = true;
    for (let d = 0; d < n && pd; d += pdStep){
      if (lineSum(n, k => at(k, (k + d) % n)) !== S) pd = false;
      else if (lineSum(n, k => at(k, ((d - k) % n + n) % n)) !== S) pd = false;
      post("testing the broken diagonals", 0.8 + d / n * 0.2);
    }
    out.pandiag = { yes: pd, sampled: pdStep > 1 };
    finish();
  };
}
const MSQ_CHECK_SRC = "function(){\n" + MSQ_KERNEL + "\n(" + msqCheckBody + ")();\n}";

/* ================= state ================= */
const msq = {
  n: 0, ready: false, method: "",
  start: 1, step: 1, sym: 0, comp: false,
  colour: "plain", trace: false, lines: true,
  hover: null, pin: null,
  target: 0n, check: null,
  pos: null, posKey: "",
  job: new Job(MSQ_CHECK_SRC),
  pz: null, sums: new Map()
};
const sym = () => SYMS[msq.sym];
/** Base value 1 … n² at the displayed (i, j). */
const baseAt = (i, j) => symCell(msq.n, SYMS[msq.sym], msq.comp, i, j);
/** Whether displayed values can leave the range a double holds exactly. */
function valuesNeedBig(){
  const nn = msq.n * msq.n;
  return Math.abs(msq.start) + nn * Math.abs(msq.step) > Number.MAX_SAFE_INTEGER;
}
/** A displayed value from its base value (exact while n ≤ EXACT_ORDER). */
function valueText(v){
  if (msq.start === 1 && msq.step === 1) return String(v);
  if (valuesNeedBig()) return String(BigInt(msq.start) + BigInt(v - 1) * BigInt(msq.step));
  return String(msq.start + (v - 1) * msq.step);
}
/** The displayed value at (i, j) as text — exact at every order. */
function cellText(i, j){
  if (msq.n <= EXACT_ORDER) return valueText(baseAt(i, j));
  const b = symCellBig(msq.n, SYMS[msq.sym], msq.comp, i, j);
  return String(BigInt(msq.start) + (b - 1n) * BigInt(msq.step));
}
/** Text of the k-th smallest base value (1 … n²) — for widths and ranges. */
function rankText(v){
  if (msq.n <= EXACT_ORDER) return valueText(v);
  return String(BigInt(msq.start) + (BigInt(v) - 1n) * BigInt(msq.step));
}
const nnText = () => String(BigInt(msq.n) * BigInt(msq.n));
const valueNum = v => msq.start + (v - 1) * msq.step;
/** The common sum of every line, for first number a and step d: n·a + d·n(n² − 1)/2. */
function magicConstant(){
  const n = BigInt(msq.n);
  return n * BigInt(msq.start) + BigInt(msq.step) * (n * (n * n - 1n) / 2n);
}
/** Turn a sum of base values on one line into the sum of the displayed values. */
const lineValue = baseSum => BigInt(msq.n) * BigInt(msq.start) + BigInt(msq.step) * (baseSum - BigInt(msq.n));

/** Widest number in the square, in characters. */
function valueWidth(){
  const last = BigInt(msq.start) + (BigInt(msq.n) * BigInt(msq.n) - 1n) * BigInt(msq.step);
  return Math.max(String(msq.start).length, String(last).length);
}
const lastText = () => String(BigInt(msq.start) + (BigInt(msq.n) * BigInt(msq.n) - 1n) * BigInt(msq.step));
/** Largest legible font for a cell that has to hold the widest value in the square. */
function cellFont(cell){
  return Math.min(cell * 0.42, (cell * 0.86) / (valueWidth() * 0.60));   // mono advance ≈ 0.6 em
}
const MSQ_TEXT_MIN = 6;        // px: below this a number is a smudge, so draw the heat map
const MSQ_GRID_MIN = 2.5;      // px: the smallest cell that can still carry a visible border
const READ_FONT = 13;          // px: the size the square opens at when the fit is too small to read
/** Cell size at which every number in the square is comfortably readable. */
function readableCell(){
  return Math.max(READ_FONT / 0.42, READ_FONT * valueWidth() * 0.60 / 0.86);
}
/** "an 8-digit", "a 5-digit" — English, not string concatenation. */
function article(d){ return (d === 8 || d === 11 || d === 18 ? "an " : "a ") + d + "-digit"; }

/* ---- colour ---- */
function heat(v, max, dark){
  const t = max > 1 ? (v - 1) / (max - 1) : 0;
  const l = dark ? (16 + t * 50) / 100 : (94 - t * 56) / 100;
  const rgb = hslToRgb(232 - t * 40, .62, l);
  return { rgb, bg: rgbCss(rgb), fg: l < .54 ? "#F4F7FB" : "#101722" };
}
/** A colour function for the current mode: (base value) → {rgb, fg}. Cached ramps keep it cheap. */
function colourer(mode, dark){
  const n = msq.n, max = n * n;
  if (mode === "heat"){
    const ramp = Array.from({ length: 256 }, (_, k) => heat(1 + k * (max - 1) / 255, max, dark));
    return v => ramp[max > 1 ? Math.round((v - 1) * 255 / (max - 1)) : 0];
  }
  if (mode === "parity"){
    const odd = { rgb: dark ? [74, 64, 160] : [208, 205, 250] }, even = { rgb: dark ? [16, 104, 110] : [190, 236, 238] };
    odd.fg = even.fg = dark ? "#F4F7FB" : "#101722";
    odd.bg = rgbCss(odd.rgb); even.bg = rgbCss(even.rgb);
    const big = valuesNeedBig();
    return v => {
      const odd_ = big ? (BigInt(msq.start) + BigInt(v - 1) * BigInt(msq.step)) % 2n !== 0n : Math.abs(valueNum(v)) % 2 === 1;
      return odd_ ? odd : even;
    };
  }
  if (mode === "residue"){
    const lut = Array.from({ length: 256 }, (_, k) => {
      const rgb = hslToRgb(k * 360 / 256, dark ? .55 : .7, dark ? .36 : .8);
      return { rgb, bg: rgbCss(rgb), fg: dark ? "#F4F7FB" : "#101722" };
    });
    return v => {
      const val = valueNum(v), r = ((val % n) + n) % n;
      return lut[Math.floor(r * 256 / n) & 255];
    };
  }
  return null;
}

/* ---- painting ---- */
const HEAT_BUDGET = 1.6e6;             // sampled pixels per interactive paint
const EXPORT_HEAT_BUDGET = 1.6e7;      // a one-off export can afford ten times as many
/* Below the size where a cell can carry a border the square is drawn as colour alone,
   and an n×n bitmap is impossible at a large order, so sample: one closed-form lookup
   per destination pixel, which costs the same whether the order is 500 or 500 000. */
function paintSampled(ctx, cell, colourOf, vis, budget){
  const n = msq.n, side = n * cell;
  const x0 = Math.max(0, Math.floor(vis ? vis.x0 : 0)), y0 = Math.max(0, Math.floor(vis ? vis.y0 : 0));
  const x1 = Math.min(side, Math.ceil(vis ? vis.x1 : side)), y1 = Math.min(side, Math.ceil(vis ? vis.y1 : side));
  const w = Math.max(1, Math.round(x1 - x0)), h = Math.max(1, Math.round(y1 - y0));
  const q = Math.min(1, Math.sqrt((budget || HEAT_BUDGET) / (w * h)));
  const bw = Math.max(1, Math.round(w * q)), bh = Math.max(1, Math.round(h * q));
  const buf = document.createElement("canvas");
  buf.width = bw; buf.height = bh;
  const bctx = buf.getContext("2d"), img = bctx.createImageData(bw, bh), px = img.data;
  for (let r = 0; r < bh; r++){
    const i = Math.min(n - 1, Math.floor((y0 + (r + 0.5) * h / bh) / cell));
    for (let c = 0; c < bw; c++){
      const j = Math.min(n - 1, Math.floor((x0 + (c + 0.5) * w / bw) / cell));
      const rgb = colourOf(baseAt(i, j)).rgb, o = (r * bw + c) * 4;
      px[o] = rgb[0]; px[o+1] = rgb[1]; px[o+2] = rgb[2]; px[o+3] = 255;
    }
  }
  bctx.putImageData(img, 0, 0);
  ctx.imageSmoothingEnabled = q < 1;
  ctx.drawImage(buf, 0, 0, bw, bh, x0, y0, w, h);
}

/** Draw the square at the origin, `cell` px per cell; vis limits work to what shows. */
function paintSquare(ctx, cell, forPrint, vis, budget){
  const n = msq.n;
  if (!msq.ready) return;
  const dark = forPrint ? false : isDark();
  const fontPx = cellFont(cell), textOn = fontPx >= MSQ_TEXT_MIN;
  const mode = msq.colour === "plain" && !textOn ? "heat" : msq.colour;
  const colourOf = colourer(mode, dark);
  const side = n * cell;

  let i0 = 0, i1 = n - 1, j0 = 0, j1 = n - 1;
  if (vis){
    j0 = clamp(Math.floor(vis.x0 / cell), 0, n - 1); j1 = clamp(Math.ceil(vis.x1 / cell), 0, n - 1);
    i0 = clamp(Math.floor(vis.y0 / cell), 0, n - 1); i1 = clamp(Math.ceil(vis.y1 / cell), 0, n - 1);
  }
  const lineInk = forPrint ? "#9AA1B4" : cssVar("--grid-ink") || "#9AA1B4";

  if (cell < MSQ_GRID_MIN){
    paintSampled(ctx, cell, colourOf, vis, budget);
  } else {
    const boxes = cell >= 7;
    const plainBg = dark ? "#121827" : "#FFFFFF";
    if (textOn){
      ctx.font = "500 " + fontPx.toFixed(1) + "px \"JetBrains Mono\", ui-monospace, monospace";
      ctx.textAlign = "center";
      ctx.textBaseline = "middle";
    }
    ctx.lineWidth = 1;
    for (let i = i0; i <= i1; i++) for (let j = j0; j <= j1; j++){
      const v = baseAt(i, j), x = j * cell, y = i * cell;
      let fg = dark ? "#E9ECF5" : "#10131C";
      if (colourOf){ const c = colourOf(v); ctx.fillStyle = c.bg; fg = c.fg; }
      else ctx.fillStyle = plainBg;
      ctx.fillRect(x, y, cell, cell);
      if (boxes){ ctx.strokeStyle = lineInk; ctx.strokeRect(x + .5, y + .5, cell - 1, cell - 1); }
      if (textOn){
        ctx.fillStyle = fg;
        ctx.fillText(n <= EXACT_ORDER ? valueText(v) : cellText(i, j), x + cell / 2, y + cell / 2 + cell * 0.02);
      }
    }
    /* Below 7 px a boxed cell turns to mush, but the eye still has to be able to
       count cells across, so rule the grid with hairlines instead. */
    if (!boxes){
      ctx.save();
      ctx.strokeStyle = lineInk; ctx.globalAlpha = 0.55; ctx.lineWidth = Math.min(1, cell / 6);
      ctx.beginPath();
      for (let k = j0; k <= j1 + 1; k++){ const t = Math.round(k * cell) + .5; ctx.moveTo(t, i0 * cell); ctx.lineTo(t, (i1 + 1) * cell); }
      for (let k = i0; k <= i1 + 1; k++){ const t = Math.round(k * cell) + .5; ctx.moveTo(j0 * cell, t); ctx.lineTo((j1 + 1) * cell, t); }
      ctx.stroke();
      ctx.restore();
    }
  }

  if (msq.trace) paintTrace(ctx, cell, i0, i1, j0, j1, dark);

  // the two diagonals, which also sum to the magic constant
  ctx.save();
  ctx.strokeStyle = forPrint ? "rgba(79,79,224,.45)" : (dark ? "rgba(154,155,255,.5)" : "rgba(79,79,224,.38)");
  ctx.lineWidth = Math.max(1, Math.min(cell * 0.06, 4));
  ctx.beginPath();
  ctx.moveTo(0, 0); ctx.lineTo(side, side);
  ctx.moveTo(side, 0); ctx.lineTo(0, side);
  ctx.stroke();
  ctx.restore();

  if (!forPrint) paintHover(ctx, cell, side, dark);

  ctx.strokeStyle = forPrint ? "#10131C" : (dark ? "#6B7390" : "#10131C");
  ctx.lineWidth = 2;
  ctx.strokeRect(1, 1, side - 2, side - 2);
}

/** The highlighted row and column under the pointer, and a ring on a cell jumped to. */
function paintHover(ctx, cell, side, dark){
  const h = msq.lines ? msq.hover : null, p = msq.pin;
  if (h){
    const [i, j] = h;
    ctx.save();
    ctx.fillStyle = dark ? "rgba(139,139,255,.16)" : "rgba(79,79,224,.10)";
    ctx.fillRect(0, i * cell, side, cell);
    ctx.fillRect(j * cell, 0, cell, side);
    ctx.strokeStyle = dark ? "rgba(139,139,255,.85)" : "rgba(79,79,224,.8)";
    ctx.lineWidth = Math.max(1, Math.min(2, cell / 8));
    ctx.strokeRect(0, i * cell, side, cell);
    ctx.strokeRect(j * cell, 0, cell, side);
    ctx.restore();
  }
  if (p){
    const [i, j] = p;
    ctx.save();
    ctx.strokeStyle = "#F5C84B"; ctx.lineWidth = Math.max(2, Math.min(4, cell / 10));
    const pad = Math.max(2, cell * 0.08);
    ctx.strokeRect(j * cell - pad, i * cell - pad, cell + pad * 2, cell + pad * 2);
    ctx.restore();
  }
}

/* ---- the path 1 → 2 → 3 … ----
   Following the numbers in order needs to know where each value sits, which is a
   table of n² positions. It is built once per square and orientation. */
const TRACE_MAX_CELLS = 16777216;      // n = 4096: a 64 MB position table
const TRACE_DRAW_MAX = 60000;          // segments drawn per paint; zoom in for more
function tracePositions(){
  const key = msq.n + ":" + msq.sym + ":" + msq.comp;
  if (msq.posKey === key) return msq.pos;
  const n = msq.n, pos = new Int32Array(n * n + 1);
  for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) pos[baseAt(i, j)] = i * n + j;
  msq.pos = pos; msq.posKey = key;
  return pos;
}
function paintTrace(ctx, cell, i0, i1, j0, j1, dark){
  const n = msq.n, nn = n * n;
  if (nn > TRACE_MAX_CELLS) return;
  const visible = (i1 - i0 + 1) * (j1 - j0 + 1);
  if (visible > TRACE_DRAW_MAX) return;
  const pos = tracePositions();
  const chunks = 48, w = clamp(cell * 0.09, 0.8, 3.2);
  ctx.save();
  ctx.lineWidth = w; ctx.lineCap = "round"; ctx.lineJoin = "round";
  const all = visible >= nn;
  const xy = v => { const p = pos[v]; return [(p % n) * cell + cell / 2, Math.floor(p / n) * cell + cell / 2]; };
  if (all){
    for (let c = 0; c < chunks; c++){
      const a = 1 + Math.floor(c * (nn - 1) / chunks), b = 1 + Math.floor((c + 1) * (nn - 1) / chunks);
      if (b <= a) continue;
      ctx.strokeStyle = rgbCss(hslToRgb(330 - c / chunks * 250, .85, dark ? .63 : .48));
      ctx.beginPath();
      let p = xy(a); ctx.moveTo(p[0], p[1]);
      for (let v = a + 1; v <= b; v++){ p = xy(v); ctx.lineTo(p[0], p[1]); }
      ctx.stroke();
    }
  } else {
    // zoomed in: only the steps that leave a visible cell
    for (let i = i0; i <= i1; i++) for (let j = j0; j <= j1; j++){
      const v = baseAt(i, j);
      if (v >= nn) continue;
      const q = xy(v + 1);
      ctx.strokeStyle = rgbCss(hslToRgb(330 - v / nn * 250, .85, dark ? .63 : .48));
      ctx.beginPath();
      ctx.moveTo(j * cell + cell / 2, i * cell + cell / 2);
      ctx.lineTo(q[0], q[1]);
      ctx.stroke();
    }
  }
  // 1 and n² as dots
  for (const [v, col] of [[1, "#3DDC97"], [nn, "#FF6B7F"]]){
    const [x, y] = xy(v);
    ctx.fillStyle = col; ctx.beginPath(); ctx.arc(x, y, clamp(cell * 0.14, 2.5, 8), 0, Math.PI * 2); ctx.fill();
  }
  ctx.restore();
}

/* ---- line sums under the pointer ---- */
function lineSum(n, get){
  const every = Math.max(1, Math.min(4096, Math.floor(Number.MAX_SAFE_INTEGER / (n * n))));
  let total = 0n, part = 0;
  for (let k = 0; k < n; k++){
    part += get(k);
    if (k % every === every - 1){ total += BigInt(part); part = 0; }
  }
  return total + BigInt(part);
}
const LIVE_SUM_MAX = 4000000;          // past this, adding a line per pointer move would lag
function cachedSum(key, f){
  let v = msq.sums.get(key);
  if (v === undefined){
    v = lineValue(f());
    if (msq.sums.size > 4000) msq.sums.clear();
    msq.sums.set(key, v);
  }
  return v;
}
function describeCell(i, j){
  const n = msq.n;
  let s = "Row " + fmt(i + 1) + ", column " + fmt(j + 1) + " is " + fmtDigits(cellText(i, j));
  if (msq.lines && n > LIVE_SUM_MAX){
    s += "  ·  every line sums to " + fmt(msq.target) + " (a live sum here would be " + fmt(n) + " additions per move)";
  } else if (msq.lines){
    const r = cachedSum("r" + i, () => lineSum(n, k => baseAt(i, k)));
    const c = cachedSum("c" + j, () => lineSum(n, k => baseAt(k, j)));
    s += "  ·  row sum " + fmt(r) + "  ·  column sum " + fmt(c);
    if (i === j) s += "  ·  on the main diagonal";
    if (i + j === n - 1) s += "  ·  on the anti-diagonal";
  }
  return s;
}

/* ---- the pan/zoom source ----
   Content units are cells. The square opens fitted when the numbers are readable at
   that size, and otherwise zoomed in on the top-left corner at a readable size, so
   the numbers are always what you see first, whatever the order. */
function msqSource(){
  const n = msq.n;
  return {
    kind: "msq", w: n, h: n, pad: 14, maxScale: 220,
    title: fmt(n) + " × " + fmt(n) + " magic square",
    meta: "every line sums to " + fmt(msq.target),
    filename: msqName("png"),
    paint(ctx, s, vis){ paintSquare(ctx, s, false, vis); },
    probe(x, y){
      const j = Math.floor(x), i = Math.floor(y);
      if (i < 0 || j < 0 || i >= n || j >= n) return "";
      return describeCell(i, j);
    },
    home(pz){
      const fit = pz.fitScale();
      if (cellFont(fit) >= 10) pz.fit();
      else pz.cornerOn(-12 / readableCell(), -12 / readableCell(), readableCell());
    },
    detail(pz){
      const v = pz.visibleContent();
      pz.centerOn((v.x0 + v.x1) / 2, (v.y0 + v.y1) / 2, Math.max(pz.s, readableCell()));
    },
    zoomNote: s => (s < 1 ? s.toPrecision(3) : s.toFixed(1)) + " px per cell  ·  " + fmt(BigInt(n) * BigInt(n)) + " cells",
    png: msqPng,
    pngNote: () => msqPngPlan().numbers ? null
      : "a PNG is fixed pixels, so at this order it can only be the colour map. Save the HTML for the real values."
  };
}

function updateViewNote(pz){
  if (!msq.ready) return;
  const v = pz.visibleContent(), n = msq.n;
  const r0 = clamp(Math.floor(v.y0), 0, n - 1) + 1, r1 = clamp(Math.ceil(v.y1), 1, n);
  const c0 = clamp(Math.floor(v.x0), 0, n - 1) + 1, c1 = clamp(Math.ceil(v.x1), 1, n);
  const all = r0 === 1 && c0 === 1 && r1 === n && c1 === n;
  const legible = cellFont(pz.s) >= MSQ_TEXT_MIN;
  $("msqNote").textContent = (all ? "all " + fmt(n) + " × " + fmt(n) : "rows " + fmt(r0) + "–" + fmt(r1)
    + ", columns " + fmt(c0) + "–" + fmt(c1)) + "  ·  " + (pz.s < 1 ? pz.s.toFixed(3) : pz.s.toFixed(1)) + " px per cell"
    + (legible ? "" : "  ·  colour map — zoom in for numbers");
}

/* ================= build ================= */
function readInt(id, fallback){
  const el = $(id), raw = el.value.trim();
  let v;
  try { v = raw ? parseBig(raw) : BigInt(fallback); } catch (e) { v = null; }
  if (v === null || v > BigInt(Number.MAX_SAFE_INTEGER) || v < -BigInt(Number.MAX_SAFE_INTEGER)){
    el.classList.add("invalid");
    return null;
  }
  el.classList.remove("invalid");
  return Number(v);
}

function buildSquare(){
  const n = parseCount($("msqOrder").value);
  if (!Number.isFinite(n) || n < 1){
    $("msqOrder").classList.add("invalid");
    toast("Type an order: any whole number from 1 up — 9, 100, 25000, 1e6 …", true);
    return;
  }
  $("msqOrder").classList.remove("invalid");
  $("msqOrder").value = fmt(n);
  const start = readInt("msqStart", 1), step = readInt("msqStep", 1);
  if (start === null || step === null){ toast("First number and step must be whole numbers", true); return; }
  if (step === 0){ $("msqStep").classList.add("invalid"); toast("A step of 0 makes every cell the same — pick any other step", true); return; }
  msq.start = start; msq.step = step;

  const notice = $("msqNotice");
  msq.job.cancel();
  if (n === 2){
    msq.ready = false; msq.n = 2;
    $("msqStats").innerHTML = "";
    $("msqTitle").textContent = "No 2 × 2 square exists";
    $("msqNote").textContent = "—";
    $("msqHover").textContent = "Type any other order and the square appears here.";
    notice.hidden = false;
    notice.innerHTML = "<strong>Order 2 is impossible.</strong> The magic constant would be 5, "
      + "but 1 and 4 cannot share a line with any pair that also sums to 5 — every "
      + "arrangement of 1, 2, 3, 4 leaves some row or column off the mark. "
      + "Every other order from 1 upward works.";
    const cv = $("msqCanvas");
    cv.getContext("2d").clearRect(0, 0, cv.width, cv.height);
    return;
  }
  notice.hidden = true;

  msq.n = n; msq.ready = true;
  msq.target = magicConstant(); msq.sums.clear(); msq.hover = null; msq.pin = null;
  if (msq.posKey && !msq.posKey.startsWith(n + ":")){ msq.pos = null; msq.posKey = ""; }
  if (msq.trace && n * n > TRACE_MAX_CELLS){
    msq.trace = false;
    $("msqTrace").setAttribute("aria-pressed", "false");
  }
  $("msqTitle").textContent = fmt(n) + " × " + fmt(n) + " magic square";
  renderMsqStats();
  msq.pz.setSource(msqSource());
  if (viewer.open && viewer.src && viewer.src.kind === "msq") viewer.show(msqSource());
  runCheck();
}

function variantName(){
  const t = sym();
  const names = { "000": "original", "001": "mirrored", "010": "flipped", "011": "rotated 180°",
                  "100": "transposed", "101": "rotated 90°", "110": "rotated 270°", "111": "anti-transposed" };
  return names["" + t.swap + t.fi + t.fj] + (msq.comp ? ", complemented" : "");
}

function renderMsqStats(){
  const n = msq.n, c = msq.check;
  const lo = rankText(1), hi = lastText();
  const tri = (r, what) => !r ? (c ? "not checked at this order" : "checking…")
    : r.yes ? "yes" + (r.sampled ? " (sampled)" : "") + " — " + what : "no";
  statTiles($("msqStats"), [
    ["Order", fmt(n) + " × " + fmt(n) + "<small>" + fmt(BigInt(n) * BigInt(n)) + " cells</small>"],
    ["Magic constant", fmt(msq.target), "big"],
    ["Numbers", (msq.step > 0 ? fmtDigits(lo) + " … " + fmtDigits(hi) : fmtDigits(hi) + " … " + fmtDigits(lo)) + (msq.step !== 1 ? "<small>step " + fmt(msq.step) + "</small>" : "")],
    ["View", variantName()],
    ["Verified", c ? c.scope + "<small>checked in " + fmtMs(c.ms) + "</small>" : "checking…", c ? (c.ok ? "ok" : "bad") : ""],
    ["Associative", tri(c && c.assoc, "cells opposite the centre pair up")],
    ["Pandiagonal", tri(c && c.pandiag, "broken diagonals are magic too")]
  ]);
}

async function runCheck(){
  const n = msq.n, key = n + ":" + msq.sym + ":" + msq.comp;
  msq.check = null;
  renderMsqStats();
  try {
    const res = await msq.job.run({ n, t: sym(), comp: msq.comp }, p => {
      const cell = $("msqStats").querySelector("div:nth-child(5) dd");
      if (cell) cell.innerHTML = "checking… " + Math.round(p.frac * 100) + "%<small>" + p.phase + "</small>";
    });
    if (key !== msq.n + ":" + msq.sym + ":" + msq.comp) return;
    msq.check = res;
    renderMsqStats();
  } catch (err){
    if (!err.cancelled) toast("The check stopped: " + explainError(err), true);
  }
}

/* A transform changes where numbers sit but never whether the square is magic, so
   the view is kept and only the overlays' caches are dropped. */
function afterTransform(){
  msq.sums.clear();
  msq.pz.thumb = null;
  msq.pz.paint();
  viewer.repaint();
  renderMsqStats();
  runCheck();
}

/* ================= exports ================= */
/* A PNG wants cells big enough for the widest number, but a canvas has a ceiling:
   past roughly 12 000 px a side the browser refuses or runs out of memory. */
const PNG_MAX_SIDE = 8000;
function msqPngPlan(){
  const n = msq.n, digits = valueWidth();
  const legible = Math.ceil((MSQ_TEXT_MIN + 1) * digits * 0.60 / 0.86);
  const want = Math.max(Math.round(legible * 1.5), Math.min(84, Math.round(640 / n)));
  const cell = Math.min(want, PNG_MAX_SIDE / n);
  return { cell, numbers: cellFont(cell) >= MSQ_TEXT_MIN };
}
function msqPng(){
  const n = msq.n, cell = msqPngPlan().cell;
  const pad = Math.max(18, Math.round(cell * 0.6)), foot = Math.max(22, Math.round(cell * 0.8));
  const size = Math.max(1, Math.round(n * cell));
  const out = document.createElement("canvas");
  out.width = size + pad * 2; out.height = size + pad * 2 + foot;
  const ctx = out.getContext("2d");
  ctx.fillStyle = "#FFFFFF";
  ctx.fillRect(0, 0, out.width, out.height);
  ctx.save(); ctx.translate(pad, pad);
  paintSquare(ctx, cell, true, null, EXPORT_HEAT_BUDGET);
  ctx.restore();
  ctx.fillStyle = "#4A5565";
  ctx.font = Math.max(11, Math.round(cell * 0.3)) + "px \"JetBrains Mono\", monospace";
  ctx.textAlign = "left"; ctx.textBaseline = "alphabetic";
  ctx.fillText(n + " × " + n + " magic square — every row, column and diagonal sums to " + fmt(msq.target),
    pad, out.height - Math.round(pad * 0.5));
  return out;
}

const SVG_CELL = 64;
const SVG_MAX_CELLS = 262144;          // order 512; past that the file stops being usable
function msqSvg(){
  const n = msq.n, cell = SVG_CELL, side = n * cell, pad = Math.round(cell * 0.5), foot = Math.round(cell * 0.9);
  const W = side + pad * 2, H = side + pad * 2 + foot, font = cellFont(cell);
  const colourOf = colourer(msq.colour, false);
  const out = ['<?xml version="1.0" encoding="UTF-8"?>\n<svg xmlns="http://www.w3.org/2000/svg" '
    + 'width="' + W + '" height="' + H + '" viewBox="0 0 ' + W + ' ' + H + '">'];
  out.push('<title>' + n + ' × ' + n + ' magic square</title>');
  out.push('<style>text{font-family:"JetBrains Mono",ui-monospace,monospace;font-weight:500;font-size:'
    + font.toFixed(2) + 'px;text-anchor:middle;dominant-baseline:central;fill:#101722}'
    + 'text.lt{fill:#F4F7FB}.cap{font-size:' + Math.max(13, cell * 0.3).toFixed(1) + 'px;text-anchor:start;fill:#4A5565}</style>');
  out.push('<rect width="' + W + '" height="' + H + '" fill="#FFFFFF"/>');
  out.push('<g transform="translate(' + pad + ',' + pad + ')">');
  if (colourOf){
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++)
      out.push('<rect x="' + (j * cell) + '" y="' + (i * cell) + '" width="' + cell + '" height="' + cell
        + '" fill="' + colourOf(baseAt(i, j)).bg + '"/>');
  }
  let d = "";
  for (let k = 0; k <= n; k++){ const p = k * cell; d += "M0 " + p + "H" + side + "M" + p + " 0V" + side; }
  out.push('<path d="' + d + '" fill="none" stroke="#9AA1B4" stroke-width="1"/>');
  out.push('<path d="M0 0L' + side + ' ' + side + 'M' + side + ' 0L0 ' + side
    + '" fill="none" stroke="#4F4FE0" stroke-opacity=".45" stroke-width="' + (cell * 0.06).toFixed(2) + '"/>');
  out.push('<rect x="1" y="1" width="' + (side - 2) + '" height="' + (side - 2) + '" fill="none" stroke="#101722" stroke-width="2"/>');
  const half = cell / 2;
  for (let i = 0; i < n; i++){
    const y = i * cell + half;
    for (let j = 0; j < n; j++){
      const v = baseAt(i, j), light = colourOf && colourOf(v).fg !== "#101722";
      out.push('<text' + (light ? ' class="lt"' : '') + ' x="' + (j * cell + half) + '" y="' + y + '">' + valueText(v) + '</text>');
    }
  }
  out.push('</g>');
  out.push('<text class="cap" x="' + pad + '" y="' + (H - Math.round(foot * 0.35)) + '">' + n + ' × ' + n
    + ' magic square — every row, column and diagonal sums to ' + fmt(msq.target) + '</text>');
  out.push('</svg>');
  return out.join("");
}

const CSV_MAX_CELLS = 4e6;             // order 2 000; past that the text file stops being openable
function msqCsv(){
  const n = msq.n, rows = new Array(n), line = new Array(n);
  for (let i = 0; i < n; i++){
    for (let j = 0; j < n; j++) line[j] = valueText(baseAt(i, j));
    rows[i] = line.join(",");
  }
  return rows.join("\r\n") + "\r\n";
}

/* ---- HTML: the square as a tiny self-contained zoomable page ----
   A raster image only holds the pixels it was saved with; this writes a page that
   carries the closed form instead — a few kilobytes at any order, opens offline in
   any browser, and draws the real numbers however far you zoom. The generator is
   serialised from the live functions, so the file cannot drift from this page. */
function msqHtmlDoc(){
  const n = msq.n, title = fmt(n) + " × " + fmt(n) + " magic square";
  const css = [
    ":root{color-scheme:light dark;--bg:#F5F6FA;--ink:#10131C;--dim:#5B6275;--line:#9AA1B4;--pane:#FFFFFF}",
    "@media (prefers-color-scheme:dark){:root{--bg:#06080F;--ink:#E9ECF5;--dim:#98A0B6;--line:#4C5571;--pane:#111624}}",
    "*{box-sizing:border-box}",
    "html,body{margin:0;height:100%;background:var(--bg);color:var(--ink);font:14px/1.5 ui-sans-serif,system-ui,'Segoe UI',sans-serif}",
    "body{display:flex;flex-direction:column}",
    "header{padding:10px 14px;border-bottom:1px solid var(--line);background:var(--pane);display:flex;gap:10px 16px;align-items:baseline;flex-wrap:wrap}",
    "h1{margin:0;font-size:15px;font-weight:650}",
    ".meta{color:var(--dim);font-size:12.5px}",
    ".tools{margin-left:auto;display:flex;gap:6px;align-items:center;flex-wrap:wrap}",
    "button,input{font:inherit;color:inherit;background:var(--bg);border:1px solid var(--line);border-radius:7px;padding:4px 9px;cursor:pointer}",
    "input{width:9ch;cursor:text;font-variant-numeric:tabular-nums}",
    "button:hover{border-color:var(--ink)}",
    "#stage{flex:1;min-height:0;position:relative;overflow:hidden;cursor:grab;touch-action:none}",
    "#stage.drag{cursor:grabbing}",
    "canvas{display:block;width:100%;height:100%}",
    "footer{padding:7px 14px;border-top:1px solid var(--line);background:var(--pane);color:var(--dim);font-size:12.5px;font-variant-numeric:tabular-nums;min-height:32px}"
  ].join("");
  const W = valueWidth();
  const script = [
    "const N = " + n + ", MAX = N * N, DIGITS = " + W + ";",
    "const T = " + JSON.stringify(sym()) + ", COMP = " + msq.comp + ", A0 = " + msq.start + ", D = " + msq.step + ";",
    "const CONST = " + JSON.stringify(fmt(msq.target)) + ";",
    MSQ_KERNEL,
    "const B = (i, j) => symCell(N, T, COMP, i, j);",
    "const V = (i, j) => A0 + (B(i, j) - 1) * D;",
    "const fmt = v => v.toLocaleString('en-US');",
    "const cv = document.getElementById('c'), stage = document.getElementById('stage');",
    "const read = document.getElementById('read');",
    "const S = { px: 1, ox: 0, oy: 0 };   // px per cell, and the top-left corner in cell space",
    "const ramp = [];",
    "function buildRamp(dark){",
    "  ramp.length = 0;",
    "  for (let k = 0; k < 256; k++){",
    "    const t = k / 255, l = dark ? (16 + t * 50) / 100 : (94 - t * 56) / 100;",
    "    const s = 0.62, q = l < .5 ? l * (1 + s) : l + s - l * s, pp = 2 * l - q;",
    "    const f = u => { if (u < 0) u += 1; if (u > 1) u -= 1;",
    "      if (u < 1/6) return pp + (q - pp) * 6 * u;",
    "      if (u < 1/2) return q;",
    "      if (u < 2/3) return pp + (q - pp) * (2/3 - u) * 6;",
    "      return pp; };",
    "    const h = (232 - t * 40) / 360;",
    "    ramp.push([Math.round(f(h + 1/3) * 255), Math.round(f(h) * 255), Math.round(f(h - 1/3) * 255), l]);",
    "  }",
    "}",
    "const isDark = () => matchMedia('(prefers-color-scheme: dark)').matches;",
    "const shade = v => ramp[MAX > 1 ? Math.round((v - 1) * 255 / (MAX - 1)) : 0];",
    "function size(){ const r = stage.getBoundingClientRect(); return [Math.max(1, r.width), Math.max(1, r.height)]; }",
    "function fitPx(){ const [w, h] = size(); return Math.min(w, h) / N; }",
    "function fontFor(px){ return Math.min(px * 0.42, px * 0.86 / (DIGITS * 0.6)); }",
    "function readPx(){ return Math.max(13 / 0.42, 13 * DIGITS * 0.6 / 0.86); }",
    "function clampView(){",
    "  const [w, h] = size();",
    "  S.px = Math.min(Math.max(S.px, fitPx() * 0.9), 220);",
    "  const span = N * S.px;",
    "  S.ox = span <= w ? (span - w) / 2 / S.px : Math.min(Math.max(S.ox, 0), (span - w) / S.px);",
    "  S.oy = span <= h ? (span - h) / 2 / S.px : Math.min(Math.max(S.oy, 0), (span - h) / S.px);",
    "}",
    "function draw(){",
    "  clampView();",
    "  const dark = isDark();",
    "  buildRamp(dark);",
    "  const [w, h] = size(), dpr = Math.min(devicePixelRatio || 1, 2), px = S.px;",
    "  cv.width = Math.round(w * dpr); cv.height = Math.round(h * dpr);",
    "  const ctx = cv.getContext('2d');",
    "  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);",
    "  ctx.fillStyle = dark ? '#06080F' : '#F5F6FA';",
    "  ctx.fillRect(0, 0, w, h);",
    "  if (px < 2.5){",
    "    // one closed-form lookup per screen pixel: the cost is the window, not the order",
    "    const W = Math.round(w), H = Math.round(h);",
    "    const img = ctx.createImageData(W, H), d = img.data;",
    "    for (let r = 0; r < H; r++){",
    "      const i = Math.floor(S.oy + r / px);",
    "      for (let c = 0; c < W; c++){",
    "        const j = Math.floor(S.ox + c / px), o = (r * W + c) * 4;",
    "        if (i < 0 || j < 0 || i >= N || j >= N) continue;",
    "        const g = shade(B(i, j));",
    "        d[o] = g[0]; d[o+1] = g[1]; d[o+2] = g[2]; d[o+3] = 255;",
    "      }",
    "    }",
    "    ctx.putImageData(img, 0, 0);",
    "  } else {",
    "    const i0 = Math.max(0, Math.floor(S.oy)), j0 = Math.max(0, Math.floor(S.ox));",
    "    const i1 = Math.min(N - 1, Math.floor(S.oy + h / px)), j1 = Math.min(N - 1, Math.floor(S.ox + w / px));",
    "    const font = fontFor(px), text = font >= 6;",
    "    if (text){",
    "      ctx.font = '500 ' + font.toFixed(1) + 'px ui-monospace,SFMono-Regular,Menlo,Consolas,monospace';",
    "      ctx.textAlign = 'center'; ctx.textBaseline = 'middle';",
    "    }",
    "    for (let i = i0; i <= i1; i++) for (let j = j0; j <= j1; j++){",
    "      const b = B(i, j), x = (j - S.ox) * px, y = (i - S.oy) * px, g = shade(b);",
    "      ctx.fillStyle = 'rgb(' + g[0] + ',' + g[1] + ',' + g[2] + ')';",
    "      ctx.fillRect(x, y, px, px);",
    "      if (px >= 7){",
    "        ctx.strokeStyle = dark ? 'rgba(232,237,245,.22)' : 'rgba(16,23,34,.18)';",
    "        ctx.lineWidth = 1; ctx.strokeRect(x + .5, y + .5, px - 1, px - 1);",
    "      }",
    "      if (text){ ctx.fillStyle = g[3] < .54 ? '#F4F7FB' : '#101722';",
    "        ctx.fillText(String(A0 + (b - 1) * D), x + px / 2, y + px / 2); }",
    "    }",
    "  }",
    "  document.getElementById('zoom').textContent = (px < 1 ? px.toFixed(2) : Math.round(px)) + ' px per cell';",
    "  hint(px < 2.5 ? 'zoomed out, so this is the colour map — dark low to light high. Zoom in for the numbers.'",
    "    : fontFor(px) < 6 ? 'cells are still too small for the numbers — keep zooming' : '');",
    "}",
    "let hintMsg = '', hover = '';",
    "function base(){ return fmt(N) + ' × ' + fmt(N) + '  ·  every row, column and diagonal sums to ' + CONST; }",
    "function hint(m){ hintMsg = m; if (!hover) read.textContent = m || base(); }",
    "function at(ev){",
    "  const r = stage.getBoundingClientRect();",
    "  const j = Math.floor(S.ox + (ev.clientX - r.left) / S.px);",
    "  const i = Math.floor(S.oy + (ev.clientY - r.top) / S.px);",
    "  if (i < 0 || j < 0 || i >= N || j >= N) return '';",
    "  return 'row ' + fmt(i + 1) + ', column ' + fmt(j + 1) + '  ·  ' + fmt(V(i, j))",
    "    + (i === j || i + j === N - 1 ? '  ·  on a diagonal' : '');",
    "}",
    "let drag = null;",
    "stage.addEventListener('pointermove', e => { if (drag){ S.ox = drag.ox - (e.clientX - drag.x) / S.px; S.oy = drag.oy - (e.clientY - drag.y) / S.px; draw(); return; }",
    "  hover = at(e); read.textContent = hover || hintMsg || base(); });",
    "stage.addEventListener('pointerleave', () => { hover = ''; read.textContent = hintMsg || base(); });",
    "stage.addEventListener('pointerdown', e => { drag = { x: e.clientX, y: e.clientY, ox: S.ox, oy: S.oy }; stage.setPointerCapture(e.pointerId); stage.classList.add('drag'); });",
    "stage.addEventListener('pointerup', () => { drag = null; stage.classList.remove('drag'); });",
    "function zoomAt(k, cx, cy){",
    "  const r = stage.getBoundingClientRect();",
    "  const x = cx === undefined ? r.width / 2 : cx - r.left;",
    "  const y = cy === undefined ? r.height / 2 : cy - r.top;",
    "  const ci = S.oy + y / S.px, cj = S.ox + x / S.px;",
    "  S.px = Math.min(Math.max(S.px * k, fitPx() * 0.9), 220);",
    "  S.ox = cj - x / S.px; S.oy = ci - y / S.px;",
    "  draw();",
    "}",
    "stage.addEventListener('wheel', e => { e.preventDefault(); zoomAt(Math.exp(-e.deltaY * 0.0016), e.clientX, e.clientY); }, { passive: false });",
    "stage.addEventListener('dblclick', e => zoomAt(2.2, e.clientX, e.clientY));",
    "document.getElementById('in').onclick = () => zoomAt(1.6);",
    "document.getElementById('out').onclick = () => zoomAt(1 / 1.6);",
    "document.getElementById('fit').onclick = () => { S.px = fitPx(); S.ox = S.oy = 0; draw(); };",
    "document.getElementById('nums').onclick = () => { S.px = Math.max(S.px, readPx()); draw(); };",
    "document.getElementById('go').onclick = () => {",
    "  const m = document.getElementById('cell').value.split(/[^0-9]+/).filter(Boolean).map(Number);",
    "  if (m.length < 2) return;",
    "  const i = Math.min(Math.max(m[0], 1), N) - 1, j = Math.min(Math.max(m[1], 1), N) - 1;",
    "  S.px = Math.max(S.px, readPx());",
    "  const [w, h] = size();",
    "  S.ox = j + .5 - w / 2 / S.px; S.oy = i + .5 - h / 2 / S.px;",
    "  draw();",
    "  hover = 'row ' + fmt(i + 1) + ', column ' + fmt(j + 1) + '  ·  ' + fmt(V(i, j));",
    "  read.textContent = hover;",
    "};",
    "addEventListener('keydown', e => {",
    "  if (e.target.id === 'cell'){ if (e.key === 'Enter') document.getElementById('go').onclick(); return; }",
    "  const step = Math.max(1, 40 / S.px);",
    "  if (e.key === '+' || e.key === '=') zoomAt(1.6);",
    "  else if (e.key === '-') zoomAt(1 / 1.6);",
    "  else if (e.key === 'ArrowLeft'){ S.ox -= step; draw(); }",
    "  else if (e.key === 'ArrowRight'){ S.ox += step; draw(); }",
    "  else if (e.key === 'ArrowUp'){ S.oy -= step; draw(); }",
    "  else if (e.key === 'ArrowDown'){ S.oy += step; draw(); }",
    "  else return;",
    "  e.preventDefault();",
    "});",
    "addEventListener('resize', draw);",
    "matchMedia('(prefers-color-scheme: dark)').addEventListener('change', draw);",
    "S.px = fontFor(fitPx()) >= 10 ? fitPx() : readPx(); draw(); read.textContent = base();"
  ].join("\n");

  const open = "<" + "script>", close = "<" + "/script>";
  return [
    "<!doctype html>",
    '<html lang="en"><head><meta charset="utf-8">',
    '<meta name="viewport" content="width=device-width,initial-scale=1">',
    "<title>" + title + "</title>",
    "<style>" + css + "</style></head><body>",
    "<header><h1>" + title + "</h1>",
    '<span class="meta">' + variantName() + " · every line sums to " + fmt(msq.target) + "</span>",
    '<span class="tools">',
    '<span class="meta" id="zoom">—</span>',
    '<button id="out" title="Zoom out">−</button><button id="in" title="Zoom in">+</button>',
    '<button id="fit">Fit</button><button id="nums">Numbers</button>',
    '<input id="cell" placeholder="row, col" aria-label="Go to row and column">',
    '<button id="go">Go</button>',
    "</span></header>",
    '<div id="stage"><canvas id="c"></canvas></div>',
    '<footer id="read">—</footer>',
    open + script + close,
    "</body></html>"
  ].join("\n");
}

function msqName(ext){ return "magic-square-" + msq.n + "x" + msq.n + "." + ext; }

/* ================= check your own square ================= */
function checkUserSquare(){
  const text = $("chkInput").value.trim(), out = $("chkOut");
  if (!text){ out.innerHTML = '<p class="hint">Type or paste a square first.</p>'; return; }
  let rows;
  try {
    rows = text.split(/\r?\n/).map(l => l.trim()).filter(Boolean)
      .map(l => l.split(/[\s,;|]+/).filter(Boolean).map(tok => {
        if (!/^[-+]?\d+$/.test(tok)) throw new Error("“" + tok + "” is not a whole number");
        return BigInt(tok);
      }));
  } catch (e){
    out.innerHTML = '<p class="hint">' + e.message + '.</p>';
    return;
  }
  const n = rows.length;
  const bad = rows.findIndex(r => r.length !== n);
  if (bad >= 0){
    out.innerHTML = '<p class="hint">That is ' + n + ' rows, but row ' + (bad + 1) + ' has ' + rows[bad].length
      + ' numbers — a square needs ' + n + ' in every row.</p>';
    return;
  }
  const rs = rows.map(r => r.reduce((a, b) => a + b, 0n));
  const cs = rows[0].map((_, j) => rows.reduce((a, r) => a + r[j], 0n));
  let d1 = 0n, d2 = 0n;
  for (let k = 0; k < n; k++){ d1 += rows[k][k]; d2 += rows[k][n - 1 - k]; }
  const total = rs.reduce((a, b) => a + b, 0n);
  const N = BigInt(n);
  const target = total % N === 0n ? total / N : null;
  const counts = new Map();
  rows.forEach(r => r.forEach(v => counts.set(String(v), (counts.get(String(v)) || 0) + 1)));
  const dups = [...counts].filter(([, c]) => c > 1).map(([v]) => v);
  const offRows = rs.map((s, i) => s !== target ? i : -1).filter(i => i >= 0);
  const offCols = cs.map((s, i) => s !== target ? i : -1).filter(i => i >= 0);
  const diagOk = d1 === target && d2 === target;
  const semi = target !== null && !offRows.length && !offCols.length;
  const magic = semi && diagOk;
  const normal = magic && !dups.length && [...counts.keys()].every(v => { const x = BigInt(v); return x >= 1n && x <= N * N; });
  let verdict, colour;
  if (magic && !dups.length){ verdict = normal ? "A normal magic square — the numbers 1 to " + fmt(n * n) + ", every line " + fmt(target)
      : "Magic — every row, column and diagonal sums to " + fmt(target); colour = "var(--good)"; }
  else if (magic){ verdict = "Every line sums to " + fmt(target) + ", but some numbers repeat"; colour = "var(--mark)"; }
  else if (semi){ verdict = "Semi-magic — rows and columns sum to " + fmt(target) + ", the diagonals don’t"; colour = "var(--mark)"; }
  else { verdict = "Not magic"; colour = "var(--bad)"; }

  const lines = [];
  if (target === null) lines.push("The total " + fmt(total) + " does not divide by " + n + ", so the lines can never all agree.");
  else {
    offRows.slice(0, 12).forEach(i => lines.push("Row " + (i + 1) + " sums to " + fmt(rs[i]) + ", not " + fmt(target)));
    offCols.slice(0, 12).forEach(j => lines.push("Column " + (j + 1) + " sums to " + fmt(cs[j]) + ", not " + fmt(target)));
    if (d1 !== target) lines.push("The main diagonal sums to " + fmt(d1));
    if (d2 !== target) lines.push("The anti-diagonal sums to " + fmt(d2));
  }
  if (dups.length) lines.push("Repeated: " + dups.slice(0, 12).join(", ") + (dups.length > 12 ? " …" : ""));

  let html = '<div class="chk-verdict"><span class="dot" style="background:' + colour + '"></span>' + verdict + '</div>';
  if (n <= 40){
    const dupSet = new Set(dups), cls = s => 'sum' + (s !== target ? " off" : "");
    html += '<table class="chk-grid"><tbody>';
    for (let i = 0; i < n; i++){
      html += "<tr>" + rows[i].map((v, j) => '<td class="' + (dupSet.has(String(v)) ? "dup " : "")
        + (i === j || i + j === n - 1 ? "diag" : "") + '">' + v + "</td>").join("")
        + '<td class="' + cls(rs[i]) + '">' + rs[i] + "</td></tr>";
    }
    html += "<tr>" + cs.map(s => '<td class="' + cls(s) + '">' + s + "</td>").join("")
      + '<td class="' + cls(d1) + '" title="main diagonal">↘ ' + d1 + "</td></tr>";
    html += "</tbody></table>";
    html += '<p class="hint">Row sums at the right, column sums underneath, the main diagonal in the corner; anti-diagonal ' + d2 + '.</p>';
  }
  if (lines.length) html += '<ul class="chk-list">' + lines.map(l => "<li>" + l + "</li>").join("") + "</ul>";
  out.innerHTML = html;
}

/* ================= wiring ================= */
function initMagic(){
  msq.pz = new PanZoom($("msqStage"), {
    onProbe: (txt, x, y) => {
      const n = msq.n, i = Math.floor(y), j = Math.floor(x);
      const inside = msq.ready && i >= 0 && j >= 0 && i < n && j < n;
      const key = inside ? i + "," + j : "";
      if ((msq.hover ? msq.hover.join(",") : "") !== key){
        msq.hover = inside ? [i, j] : null;
        if (msq.lines) msq.pz.paint();
      }
      $("msqHover").textContent = txt || "Point at a cell to read it and the sums of its row and column.";
    },
    onLeave: () => { if (msq.hover){ msq.hover = null; msq.pz.paint(); } },
    onPaint: updateViewNote
  });
  $("msqBuild").addEventListener("click", buildSquare);
  ["msqOrder", "msqStart", "msqStep"].forEach(id =>
    $(id).addEventListener("keydown", e => { if (e.key === "Enter") buildSquare(); }));
  $("msqPresets").addEventListener("click", e => {
    const b = e.target.closest("button[data-n]");
    if (!b) return;
    $("msqOrder").value = fmt(+b.dataset.n);
    buildSquare();
  });
  $("msqRotate").addEventListener("click", () => { if (!msq.ready) return; msq.sym = symCompose(msq.sym, ROTATE_CW); afterTransform(); });
  $("msqMirror").addEventListener("click", () => { if (!msq.ready) return; msq.sym = symCompose(msq.sym, MIRROR_LR); afterTransform(); });
  $("msqComplement").addEventListener("click", () => {
    if (!msq.ready) return;
    msq.comp = !msq.comp;
    $("msqComplement").setAttribute("aria-pressed", String(msq.comp));
    afterTransform();
  });
  $("msqShuffle").addEventListener("click", () => {
    if (!msq.ready) return;
    let k, c;
    do { k = Math.floor(Math.random() * 8); c = Math.random() < 0.5; } while (k === msq.sym && c === msq.comp);
    msq.sym = k; msq.comp = c;
    $("msqComplement").setAttribute("aria-pressed", String(c));
    afterTransform();
  });
  $("msqReset").addEventListener("click", () => {
    msq.sym = 0; msq.comp = false;
    $("msqComplement").setAttribute("aria-pressed", "false");
    if (msq.ready) afterTransform();
  });
  segWire($("msqColour"), "m", m => { msq.colour = m; msq.pz.thumb = null; msq.pz.paint(); viewer.repaint(); });
  $("msqTrace").addEventListener("click", () => {
    if (!msq.ready) return;
    if (!msq.trace && msq.n * msq.n > TRACE_MAX_CELLS){
      toast("The path needs a table of where every number sits — n² entries — so it is drawn up to order 4,096", true);
      return;
    }
    msq.trace = !msq.trace;
    $("msqTrace").setAttribute("aria-pressed", String(msq.trace));
    if (msq.trace && msq.n > 245) toast("Zoom in to follow the path — it is drawn for the cells on screen");
    msq.pz.paint(); viewer.repaint();
  });
  $("msqLines").addEventListener("click", () => {
    msq.lines = !msq.lines;
    $("msqLines").setAttribute("aria-pressed", String(msq.lines));
    msq.pz.paint();
  });
  const go = () => {
    if (!msq.ready) return;
    const m = $("msqGoto").value.split(/[^0-9]+/).filter(Boolean).map(Number);
    if (m.length < 2){ toast("Type a row and a column, like 120, 45", true); return; }
    const i = clamp(m[0], 1, msq.n) - 1, j = clamp(m[1], 1, msq.n) - 1;
    msq.pin = [i, j];
    msq.pz.centerOn(j + 0.5, i + 0.5, Math.max(msq.pz.s, readableCell()));
    $("msqHover").textContent = describeCell(i, j);
  };
  $("msqGo").addEventListener("click", go);
  $("msqGoto").addEventListener("keydown", e => { if (e.key === "Enter") go(); });
  $("msqNumbers").addEventListener("click", () => { if (msq.ready) msqSource().detail(msq.pz); });
  const open = () => { if (msq.ready) viewer.show(msqSource()); };
  $("msqFull").addEventListener("click", open);

  const has = () => { if (msq.ready) return true; toast("Build a square first", true); return false; };
  $("msqSavePng").addEventListener("click", () => {
    if (!has()) return;
    const plan = msqPngPlan();
    savePng(msqPng(), msqName("png"), plan.numbers ? null
      : "a PNG is fixed pixels, so at order " + fmt(msq.n) + " it can only be the colour map — save the HTML for the real numbers");
  });
  $("msqSaveSvg").addEventListener("click", () => {
    if (!has()) return;
    if (msq.n * msq.n > SVG_MAX_CELLS){
      toast("An SVG with " + fmt(msq.n * msq.n) + " numbers would not open in anything; SVG stops at order 512 — the HTML stays small at any order and shows the real numbers", true);
      return;
    }
    requestAnimationFrame(() => saveText(msqSvg(), msqName("svg"), "image/svg+xml", "vector, every number stays sharp"));
  });
  $("msqSaveCsv").addEventListener("click", () => {
    if (!has()) return;
    if (msq.n * msq.n > CSV_MAX_CELLS){
      toast("A CSV of " + fmt(msq.n * msq.n) + " numbers is too big for a spreadsheet to open; CSV stops at order 2,000 — save the HTML instead", true);
      return;
    }
    requestAnimationFrame(() => saveText(msqCsv(), msqName("csv"), "text/csv", fmt(msq.n) + " rows of " + fmt(msq.n)));
  });
  $("msqSaveHtml").addEventListener("click", () => {
    if (!has()) return;
    saveText(msqHtmlDoc(), msqName("html"), "text/html", "a page that redraws the real numbers at any zoom");
  });

  $("chkRun").addEventListener("click", checkUserSquare);
  $("chkInput").addEventListener("keydown", e => { if (e.key === "Enter" && (e.ctrlKey || e.metaKey)) checkUserSquare(); });
  $("chkClear").addEventListener("click", () => { $("chkInput").value = ""; $("chkOut").innerHTML = ""; });
  $("chkLoad").addEventListener("click", () => {
    if (!has()) return;
    if (msq.n > 100){ toast("Loading pastes every number into the box, so it takes squares up to order 100", true); return; }
    const n = msq.n, w = valueWidth(), lines = [];
    for (let i = 0; i < n; i++){
      const row = [];
      for (let j = 0; j < n; j++) row.push(valueText(baseAt(i, j)).padStart(w));
      lines.push(row.join(" "));
    }
    $("chkInput").value = lines.join("\n");
    checkUserSquare();
  });
  themeListeners.push(() => { if (msq.ready){ msq.pz.thumb = null; msq.pz.paint(); } });
}
