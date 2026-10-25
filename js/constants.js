"use strict";
/* ================= constants: the worker =================
   Runs off the main thread, so there is no ceiling on the number of places — only
   time and memory. Every constant comes out as floor(x · 10^prec) in a BigInt and
   the decimal string is cut from that. 20 guard digits absorb truncation error. */
function constantsWorker(){
  const C3_OVER_24 = 10939058860032000n;

  /* Chudnovsky with binary splitting. Indices stay Numbers (they never pass a few
     million); only the leaves turn them into BigInts. */
  let leavesDone = 0, leavesTotal = 1, lastPost = 0;
  function tick(){
    leavesDone++;
    const f = leavesDone / leavesTotal;
    if (f - lastPost >= 0.01){ lastPost = f; post("summing the Chudnovsky series", f * 0.4); }
  }
  function bs(a, b){
    if (b - a === 1){
      tick();
      if (a === 0) return [1n, 1n, 13591409n];
      const A = BigInt(a);
      const P = (6n*A - 5n) * (2n*A - 1n) * (6n*A - 1n);
      const Q = A*A*A * C3_OVER_24;
      let T = P * (13591409n + 545140134n*A);
      if (a & 1) T = -T;
      return [P, Q, T];
    }
    const m = Math.floor((a + b) / 2);
    const [Pam, Qam, Tam] = bs(a, m);
    const [Pmb, Qmb, Tmb] = bs(m, b);
    return [Pam*Pmb, Qam*Qmb, Qmb*Tam + Pam*Tmb];
  }

  /* e = Σ 1/k!, split the same way: es(a, b) gives P/Q = Σ_{k=a+1..b} 1/((a+1)…k). */
  function es(a, b){
    if (b - a === 1){ tick(); return [1n, BigInt(b)]; }
    const m = Math.floor((a + b) / 2);
    const [P1, Q1] = es(a, m), [P2, Q2] = es(m, b);
    return [P1*Q2 + P2, Q1*Q2];
  }

  function bitLen(n){
    const h = n.toString(16);
    return (h.length - 1) * 4 + (32 - Math.clz32(parseInt(h[0], 16)));
  }
  /* Integer square root by recursion on the top half of the bits, then Newton from
     above: each level doubles the correct bits, so the full-size division only runs
     a couple of times instead of once per bit of precision. */
  function isqrt(n){
    if (n < 4503599627370496n){
      let r = BigInt(Math.floor(Math.sqrt(Number(n))));
      while (r * r > n) r--;
      while ((r + 1n) * (r + 1n) <= n) r++;
      return r;
    }
    const k = BigInt(Math.floor((bitLen(n) - 1) / 4));
    let x = (isqrt(n >> (2n * k)) + 1n) << k;
    for (;;){
      const y = (x + n / x) >> 1n;
      if (y >= x) return x;
      x = y;
    }
  }

  function post(phase, frac){ postMessage({ type: "progress", phase, frac }); }

  function scaled(c, prec){
    const one = 10n ** BigInt(prec);
    if (c === "pi"){
      const terms = Math.floor(prec / 14.181647462725477) + 2;
      leavesTotal = terms;
      const [, Q, T] = bs(0, terms);
      post("taking the square root of 10005", 0.4);
      const root = isqrt(10005n * one * one);
      post("dividing", 0.7);
      return (Q * 426880n * root) / T;
    }
    if (c === "e"){
      // smallest K with K! > 10^prec, so the tail of the series is below the last digit
      let K = 1, lg = 0;
      while (lg < prec + 5){ K++; lg += Math.log10(K); }
      leavesTotal = K;
      const [P, Q] = es(0, K);
      post("dividing", 0.7);
      return ((P + Q) * one) / Q;
    }
    post("Newton square root", 0.2);
    if (c === "sqrt2") return isqrt(2n * one * one);
    if (c === "sqrt3") return isqrt(3n * one * one);
    if (c === "phi") return (one + isqrt(5n * one * one)) / 2n;
    throw new Error("unknown constant " + c);
  }

  onmessage = e => {
    const { c, places } = e.data;
    try {
      const t0 = performance.now();
      const prec = places + 20;
      const v = scaled(c, prec);
      post("writing out the decimal digits", 0.85);
      const s = v.toString();
      const intLen = s.length - prec;
      postMessage({ type: "done", intPart: s.slice(0, intLen), digits: s.slice(intLen, intLen + places),
        ms: performance.now() - t0 });
    } catch (err){
      postMessage({ type: "error", message: String(err && err.message || err) });
    }
  };
}

/* ================= constants: the page ================= */
const CONSTS = {
  pi:    { sym: "π",  name: "π",  title: "pi",     how: "Chudnovsky series, binary splitting" },
  e:     { sym: "e",  name: "e",  title: "e",      how: "Σ 1/k!, binary splitting" },
  phi:   { sym: "φ",  name: "φ",  title: "phi",    how: "(1 + √5) / 2, Newton square root" },
  sqrt2: { sym: "√2", name: "√2", title: "sqrt2",  how: "Newton square root" },
  sqrt3: { sym: "√3", name: "√3", title: "sqrt3",  how: "Newton square root" }
};
const K = {
  c: "pi", digits: "", intPart: "3", ms: 0,
  mode: "colour", view: "field",
  cols: 0, rows: 0,
  walk: null,
  job: new Job(constantsWorker),
  progress: null, pz: null, stream: null
};

/* ---- the digit field: one cell per place ----
   Painted straight from the digit string for just the visible window, so memory and
   paint time follow the screen, not the number of digits. */
let scratch = null;
function scratchCanvas(w, h){
  if (!scratch) scratch = document.createElement("canvas");
  if (scratch.width < w) scratch.width = w;
  if (scratch.height < h) scratch.height = h;
  return scratch;
}
function fieldSource(){
  const cols = K.cols, rows = K.rows, n = K.digits.length, digits = K.digits;
  return {
    w: cols, h: rows, maxScale: 80,
    title: fmt(n) + " decimal places of " + CONSTS[K.c].name,
    meta: (K.mode === "colour" ? "colour" : "black & white") + " · " + fmt(cols) + " × " + fmt(rows),
    filename: CONSTS[K.c].title + "-" + n + "-" + K.mode + ".png",
    paint(ctx, s, vis){
      const table = K.mode === "colour" ? PAL_RGB : GREY_RGB;
      const x0 = vis ? Math.max(0, vis.x0) : 0, y0 = vis ? Math.max(0, vis.y0) : 0;
      const x1 = vis ? Math.min(cols * s, vis.x1) : cols * s, y1 = vis ? Math.min(rows * s, vis.y1) : rows * s;
      if (x1 <= x0 || y1 <= y0) return;
      if (s >= 1){
        // one source pixel per visible digit, scaled up without smoothing
        const c0 = Math.floor(x0 / s), c1 = Math.min(cols - 1, Math.ceil(x1 / s));
        const r0 = Math.floor(y0 / s), r1 = Math.min(rows - 1, Math.ceil(y1 / s));
        const bw = c1 - c0 + 1, bh = r1 - r0 + 1;
        const buf = scratchCanvas(bw, bh), bctx = buf.getContext("2d");
        const img = bctx.createImageData(bw, bh), px = img.data;
        for (let r = 0; r < bh; r++){
          let i = (r0 + r) * cols + c0;
          for (let c = 0; c < bw; c++, i++){
            if (i >= n) break;
            const rgb = table[digits.charCodeAt(i) - 48], o = (r * bw + c) * 4;
            px[o] = rgb[0]; px[o+1] = rgb[1]; px[o+2] = rgb[2]; px[o+3] = 255;
          }
        }
        bctx.putImageData(img, 0, 0);
        ctx.imageSmoothingEnabled = false;
        ctx.drawImage(buf, 0, 0, bw, bh, c0 * s, r0 * s, bw * s, bh * s);
        if (s >= 9){
          ctx.strokeStyle = "rgba(0,0,0,.22)"; ctx.lineWidth = 1;
          ctx.beginPath();
          for (let c = c0; c <= c1 + 1; c++){ const x = Math.round(c * s) + .5; ctx.moveTo(x, r0 * s); ctx.lineTo(x, (r1 + 1) * s); }
          for (let r = r0; r <= r1 + 1; r++){ const y = Math.round(r * s) + .5; ctx.moveTo(c0 * s, y); ctx.lineTo((c1 + 1) * s, y); }
          ctx.stroke();
        }
        if (s >= 15){
          ctx.font = "600 " + Math.min(s * 0.56, 30).toFixed(1) + "px \"JetBrains Mono\", ui-monospace, monospace";
          ctx.textAlign = "center"; ctx.textBaseline = "middle";
          for (let r = r0; r <= r1; r++) for (let c = c0; c <= c1; c++){
            const i = r * cols + c;
            if (i >= n) break;
            const d = digits.charCodeAt(i) - 48, rgb = table[d];
            const lum = 0.2126 * rgb[0] + 0.7152 * rgb[1] + 0.0722 * rgb[2];
            ctx.fillStyle = lum > 150 ? "rgba(0,0,0,.78)" : "rgba(255,255,255,.92)";
            ctx.fillText(String(d), c * s + s / 2, r * s + s / 2 + s * 0.03);
          }
        }
      } else {
        // more digits than pixels: sample one digit per screen pixel
        const dx = Math.floor(x0), dy = Math.floor(y0);
        const bw = Math.max(1, Math.ceil(x1) - dx), bh = Math.max(1, Math.ceil(y1) - dy);
        const buf = scratchCanvas(bw, bh), bctx = buf.getContext("2d");
        const img = bctx.createImageData(bw, bh), px = img.data;
        for (let r = 0; r < bh; r++){
          const row = Math.min(rows - 1, Math.floor((dy + r + 0.5) / s));
          for (let c = 0; c < bw; c++){
            const i = row * cols + Math.min(cols - 1, Math.floor((dx + c + 0.5) / s));
            if (i >= n) continue;
            const rgb = table[digits.charCodeAt(i) - 48], o = (r * bw + c) * 4;
            px[o] = rgb[0]; px[o+1] = rgb[1]; px[o+2] = rgb[2]; px[o+3] = 255;
          }
        }
        bctx.putImageData(img, 0, 0);
        ctx.drawImage(buf, 0, 0, bw, bh, dx, dy, bw, bh);
      }
    },
    probe(x, y){
      const c = Math.floor(x), r = Math.floor(y);
      if (c < 0 || c >= cols || r < 0 || r >= rows) return "";
      const i = r * cols + c;
      if (i >= n) return "";
      return "Place " + fmt(i + 1) + " is " + digits[i] + "  ·  row " + fmt(r + 1) + ", column " + fmt(c + 1);
    },
    detail(pz){ const v = pz.visibleContent(); pz.centerOn((v.x0 + v.x1) / 2, (v.y0 + v.y1) / 2, 24); },
    zoomNote: s => (s < 1 ? s.toFixed(3) : s.toFixed(1)) + " px per digit  ·  " + fmt(n) + " digits",
    png(){
      const scale = cols <= 4096 ? Math.max(1, Math.min(8, Math.ceil(1400 / cols))) : 4096 / cols;
      const out = document.createElement("canvas");
      out.width = Math.max(1, Math.round(cols * scale)); out.height = Math.max(1, Math.round(rows * scale));
      const ctx = out.getContext("2d");
      ctx.fillStyle = "#FFFFFF"; ctx.fillRect(0, 0, out.width, out.height);
      this.paint(ctx, scale, null);
      return out;
    }
  };
}

/* ---- the random walk: digit d means "take one step at d × 36°" ---- */
const WALK_VECTOR_MAX = 150000;        // below this the walk is stroked as vector lines
const WALK_RASTER = 1600;              // above it, plotted into a bitmap this many px across
function buildWalk(){
  const digits = K.digits, n = digits.length;
  const cs = [], sn = [];
  for (let d = 0; d < 10; d++){ cs[d] = Math.cos(d * Math.PI / 5); sn[d] = -Math.sin(d * Math.PI / 5); }
  let x = 0, y = 0, minx = 0, maxx = 0, miny = 0, maxy = 0;
  for (let i = 0; i < n; i++){
    const d = digits.charCodeAt(i) - 48;
    x += cs[d]; y += sn[d];
    if (x < minx) minx = x; else if (x > maxx) maxx = x;
    if (y < miny) miny = y; else if (y > maxy) maxy = y;
  }
  const end = [x, y];
  const pad = 2, w = maxx - minx + pad * 2, h = maxy - miny + pad * 2;
  const walk = { n, minx: minx - pad, miny: miny - pad, w, h, end, dist: Math.hypot(x, y) };
  if (n <= WALK_VECTOR_MAX){
    const pts = new Float32Array((n + 1) * 2);
    x = 0; y = 0;
    for (let i = 0; i < n; i++){
      const d = digits.charCodeAt(i) - 48;
      x += cs[d]; y += sn[d];
      pts[(i + 1) * 2] = x; pts[(i + 1) * 2 + 1] = y;
    }
    walk.pts = pts;
  } else {
    walk.raster = rasterWalk(walk, cs, sn);
  }
  K.walk = walk;
}
function walkHue(t, dark){ return hslToRgb(200 + t * 220, 0.85, dark ? 0.62 : 0.47); }
function rasterWalk(walk, cs, sn){
  const digits = K.digits, n = digits.length, dark = isDark();
  const k = WALK_RASTER / Math.max(walk.w, walk.h);
  const W = Math.max(1, Math.ceil(walk.w * k)), H = Math.max(1, Math.ceil(walk.h * k));
  const cv = document.createElement("canvas");
  cv.width = W; cv.height = H;
  const ctx = cv.getContext("2d"), img = ctx.createImageData(W, H), px = img.data;
  const lut = Array.from({ length: 256 }, (_, i) => walkHue(i / 255, dark));
  const sub = Math.max(1, Math.ceil(k));
  let x = -walk.minx, y = -walk.miny;
  for (let i = 0; i < n; i++){
    const d = digits.charCodeAt(i) - 48, rgb = lut[Math.floor(i * 255 / n)];
    for (let t = 1; t <= sub; t++){
      const X = Math.floor((x + cs[d] * t / sub) * k), Y = Math.floor((y + sn[d] * t / sub) * k);
      const o = (Y * W + X) * 4;
      px[o] = rgb[0]; px[o+1] = rgb[1]; px[o+2] = rgb[2]; px[o+3] = 255;
    }
    x += cs[d]; y += sn[d];
  }
  ctx.putImageData(img, 0, 0);
  cv.k = k;
  return cv;
}
function walkSource(){
  const walk = K.walk, n = walk.n;
  return {
    w: walk.w, h: walk.h, maxScale: 400, minimap: true,
    title: "Random walk of " + fmt(n) + " digits of " + CONSTS[K.c].name,
    meta: "digit d steps at d × 36° · ends " + walk.dist.toFixed(1) + " steps from the start (√n ≈ " + Math.sqrt(n).toFixed(1) + ")",
    filename: CONSTS[K.c].title + "-" + n + "-walk.png",
    paint(ctx, s, vis){
      if (walk.raster){
        ctx.imageSmoothingEnabled = s / walk.raster.k < 2;
        ctx.drawImage(walk.raster, 0, 0, walk.raster.width / walk.raster.k * s, walk.raster.height / walk.raster.k * s);
      } else {
        const pts = walk.pts, dark = isDark(), ox = -walk.minx, oy = -walk.miny;
        const chunks = Math.min(96, Math.max(1, Math.ceil(n / 50)));
        ctx.lineWidth = clamp(s * 0.18, 0.6, 2.4);
        ctx.lineJoin = "round"; ctx.lineCap = "round";
        for (let c = 0; c < chunks; c++){
          const a = Math.floor(c * n / chunks), b = Math.floor((c + 1) * n / chunks);
          ctx.strokeStyle = rgbCss(walkHue(c / Math.max(1, chunks - 1), dark));
          ctx.beginPath();
          ctx.moveTo((pts[a*2] + ox) * s, (pts[a*2+1] + oy) * s);
          for (let i = a + 1; i <= b; i++) ctx.lineTo((pts[i*2] + ox) * s, (pts[i*2+1] + oy) * s);
          ctx.stroke();
        }
      }
      // start and finish
      const mark = (px, py, col) => {
        const r = clamp(s * 0.9, 3, 7);
        ctx.fillStyle = col; ctx.beginPath(); ctx.arc(px * s, py * s, r, 0, Math.PI * 2); ctx.fill();
        ctx.strokeStyle = isDark() ? "#06080F" : "#FFFFFF"; ctx.lineWidth = 1.5; ctx.stroke();
      };
      mark(-walk.minx, -walk.miny, "#3DDC97");
      mark(walk.end[0] - walk.minx, walk.end[1] - walk.miny, "#FF6B7F");
    },
    probe(){ return "green marks the first step, red the last · colour runs blue → violet → orange along the walk"; },
    zoomNote: s => (s < 1 ? s.toFixed(3) : s.toFixed(1)) + " px per step  ·  " + fmt(n) + " steps",
    png(){
      const k = 2000 / Math.max(walk.w, walk.h);
      const out = document.createElement("canvas");
      out.width = Math.ceil(walk.w * k); out.height = Math.ceil(walk.h * k);
      const ctx = out.getContext("2d");
      ctx.fillStyle = isDark() ? "#06080F" : "#FFFFFF"; ctx.fillRect(0, 0, out.width, out.height);
      this.paint(ctx, k, null);
      return out;
    }
  };
}

function currentConstSource(){
  if (!K.digits.length) return null;
  if (K.view === "walk"){ if (!K.walk) buildWalk(); return walkSource(); }
  return fieldSource();
}
function showConstFigure(keepView){
  const src = currentConstSource();
  if (!src) return;
  K.pz.setSource(src, keepView);
  $("piFigTitle").textContent = K.view === "walk" ? "Random walk" : "Digit field";
  $("piModeSeg").hidden = K.view === "walk";
  $("piGridNote").textContent = K.view === "walk"
    ? fmt(K.digits.length) + " steps · " + (K.walk.raster ? "plotted" : "vector")
    : fmt(K.cols) + " × " + fmt(K.rows) + " cells";
  $("piHover").textContent = K.view === "walk"
    ? "Each digit is a step: 0 points east, and each digit turns another 36°. Green is the start, red the finish."
    : "Point at the field to read a digit; click to jump the digit list there. Ctrl + scroll or pinch to zoom.";
  if (viewer.open && viewer.src && viewer.src.kind === "const"){ src.kind = "const"; viewer.show(src); }
}

/* ---- statistics ---- */
/** Upper tail of χ² with k degrees of freedom, via the Wilson–Hilferty normal approximation. */
function chiSquareP(x, k){
  const z = (Math.cbrt(x / k) - (1 - 2 / (9 * k))) / Math.sqrt(2 / (9 * k));
  // Φ(z) from the Abramowitz–Stegun erf approximation
  const t = 1 / (1 + 0.3275911 * Math.abs(z) / Math.SQRT2);
  const erf = 1 - (((((1.061405429 * t - 1.453152027) * t) + 1.421413741) * t - 0.284496736) * t + 0.254829592) * t
    * Math.exp(-z * z / 2);
  const phi = 0.5 * (1 + Math.sign(z) * erf);
  return 1 - phi;
}
function constStats(){
  const d = K.digits, n = d.length, counts = digitCounts(d);
  const exp = n / 10;
  let chi = 0;
  for (const c of counts) chi += (c - exp) * (c - exp) / exp;
  let best = 0, bestAt = 0, run = 1, sum = 0;
  for (let i = 0; i < n; i++){
    sum += d.charCodeAt(i) - 48;
    if (i > 0 && d.charCodeAt(i) === d.charCodeAt(i - 1)) run++; else run = 1;
    if (run > best){ best = run; bestAt = i - run + 1; }
  }
  return { counts, chi, p: chiSquareP(chi, 9), best, bestAt, sum };
}

function renderConstPage(){
  const n = K.digits.length, info = CONSTS[K.c];
  const st = constStats();
  const most = st.counts.indexOf(Math.max(...st.counts)), least = st.counts.indexOf(Math.min(...st.counts));
  statTiles($("piStats"), [
    ["Decimal places", fmt(n), "big"],
    ["Computed in", fmtMs(K.ms)],
    ["Method", info.how],
    ["Digit sum", fmt(st.sum) + "<small>mean " + (st.sum / n).toFixed(4) + " (4.5 if uniform)</small>"],
    ["Last place", "#" + fmt(n) + " is " + K.digits[n - 1]]
  ]);
  renderLegend($("piLegend"), st.counts, dg => K.mode === "colour" ? PALETTE[dg] : GREYS[dg]);
  $("piChi").textContent = "χ² = " + st.chi.toFixed(2) + ", p ≈ " + st.p.toFixed(2);
  const runDigit = K.digits[st.bestAt];
  $("piFacts").innerHTML = [
    ["Longest run of one digit", "<b>" + runDigit.repeat(Math.min(st.best, 24)) + "</b>" + (st.best > 24 ? "…" : "")
      + " — " + st.best + " in a row, starting at place " + fmt(st.bestAt + 1)],
    ["Do the digits look random?", st.p < 0.01
      ? "χ² p ≈ " + st.p.toFixed(3) + " — lopsided at this length"
      : "χ² p ≈ " + st.p.toFixed(2) + " — consistent with every digit equally likely"],
    ["Most and least frequent", most + " (" + fmt(st.counts[most]) + ") and " + least + " (" + fmt(st.counts[least]) + ")"],
    ["First 50 places", K.intPart + "." + K.digits.slice(0, 50)]
  ].map(([k, v]) => "<div><dt>" + k + "</dt><dd>" + v + "</dd></div>").join("");
  $("piLead").textContent = K.intPart + "." + K.digits.slice(0, 40) + (n > 40 ? "…" : "");
  K.stream.set(K.digits);
}

async function computeConstant(){
  const raw = $("piDigits").value;
  const n = parseCount(raw);
  if (!Number.isFinite(n) || n < 1){
    $("piDigits").classList.add("invalid");
    toast("Type a number of places, like 50000, 2.5M or 1e7", true);
    return;
  }
  $("piDigits").classList.remove("invalid");
  $("piDigits").value = fmt(n);
  const c = K.c, info = CONSTS[c];
  $("piCompute").disabled = true;
  $("piCancel").hidden = false;
  K.progress.start("computing " + fmt(n) + " places of " + info.name);
  try {
    const res = await K.job.run({ c, places: n }, p => K.progress.set(p.phase, p.frac));
    K.progress.set("drawing", 1);
    K.digits = res.digits; K.intPart = res.intPart; K.ms = res.ms; K.walk = null;
    K.cols = Math.ceil(Math.sqrt(n)); K.rows = Math.ceil(n / K.cols);
    $("piName").textContent = info.name;
    renderConstPage();
    showConstFigure(false);
    toast(fmt(n) + " places of " + info.name + " in " + fmtMs(res.ms));
  } catch (err){
    if (!err.cancelled) toast("Could not finish: " + explainError(err), true);
    else toast("Cancelled");
  } finally {
    K.progress.stop();
    $("piCompute").disabled = false;
    $("piCancel").hidden = true;
  }
}

function initConstants(){
  K.progress = new Progress($("piProgress"), $("piProgressText"));
  K.stream = new DigitStream($("piStream"), $("piStreamInner"), $("piStreamNote"));
  K.pz = new PanZoom($("piStage"), {
    onProbe: txt => { $("piHover").textContent = txt || "Point at the field to read a digit; click to jump the digit list there."; },
    onClick: (x, y) => {
      if (K.view !== "field") return;
      const c = Math.floor(x), r = Math.floor(y), i = r * K.cols + c;
      if (c >= 0 && c < K.cols && r >= 0 && i < K.digits.length) K.stream.scrollToIndex(i);
    }
  });
  segWire($("piConst"), "c", c => {
    K.c = c;
    $("piName").textContent = CONSTS[c].name;
    computeConstant();
  });
  $("piCompute").addEventListener("click", computeConstant);
  $("piCancel").addEventListener("click", () => K.job.cancel());
  $("piDigits").addEventListener("keydown", e => { if (e.key === "Enter") computeConstant(); });
  $("piPresets").addEventListener("click", e => {
    const b = e.target.closest("button[data-n]");
    if (!b) return;
    $("piDigits").value = fmt(+b.dataset.n);
    computeConstant();
  });
  const setView = v => {
    K.view = v;
    $("piViewField").setAttribute("aria-pressed", String(v === "field"));
    $("piViewWalk").setAttribute("aria-pressed", String(v === "walk"));
    showConstFigure(false);
  };
  $("piViewField").addEventListener("click", () => setView("field"));
  $("piViewWalk").addEventListener("click", () => setView("walk"));
  const setMode = m => {
    K.mode = m;
    $("piModeColour").setAttribute("aria-pressed", String(m === "colour"));
    $("piModeGrey").setAttribute("aria-pressed", String(m === "grey"));
    if (K.digits.length){
      renderLegend($("piLegend"), digitCounts(K.digits), dg => m === "colour" ? PALETTE[dg] : GREYS[dg]);
      showConstFigure(true);
    }
  };
  $("piModeColour").addEventListener("click", () => setMode("colour"));
  $("piModeGrey").addEventListener("click", () => setMode("grey"));
  const open = () => { const s = currentConstSource(); if (s){ s.kind = "const"; viewer.show(s); } };
  $("piFull").addEventListener("click", open);
  $("piSave").addEventListener("click", () => {
    const s = currentConstSource();
    if (s) savePng(s.png(), s.filename);
  });
  $("piCopy").addEventListener("click", () => {
    if (K.digits.length) copyText(K.intPart + "." + K.digits, fmt(K.digits.length) + " places");
  });
  $("piSaveTxt").addEventListener("click", () => {
    if (!K.digits.length) return;
    saveText(K.intPart + "." + K.digits + "\n", CONSTS[K.c].title + "-" + K.digits.length + ".txt", "text/plain");
  });
  themeListeners.push(() => {
    if (K.walk && K.walk.raster) K.walk = null;
    if (K.digits.length && !$("panel-pi").hidden) showConstFigure(true);
  });
}
