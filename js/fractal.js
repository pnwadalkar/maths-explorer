"use strict";
/* ================= fractals: the worker =================
   Each worker takes a band of rows and returns a smooth (fractional) escape count
   per pixel, or −1 for points that never escape. Colouring happens on the page so a
   palette change never needs a re-render. */
function fractalWorker(){
  onmessage = e => {
    const { job, band, kind, re0, im0, step, w, row0, rows, maxIter, jr, ji } = e.data;
    const out = new Float32Array(w * rows);
    const LOG2 = Math.log(2), BAIL = 256 * 256;
    for (let r = 0; r < rows; r++){
      const im = im0 - (row0 + r) * step;
      for (let c = 0; c < w; c++){
        const re = re0 + c * step;
        let x, y, cr, ci;
        if (kind === "julia"){ x = re; y = im; cr = jr; ci = ji; }
        else {
          x = 0; y = 0; cr = re; ci = kind === "ship" ? -im : im;
          if (kind === "mandel"){
            // skip the two biggest solid regions outright: the main cardioid and the period-2 bulb
            const q = (re - 0.25) * (re - 0.25) + im * im;
            if (q * (q + (re - 0.25)) <= 0.25 * im * im || (re + 1) * (re + 1) + im * im <= 0.0625){
              out[r * w + c] = -1; continue;
            }
          }
        }
        let n = 0, xx = x * x, yy = y * y;
        if (kind === "ship"){
          while (n < maxIter && xx + yy <= BAIL){
            const ax = Math.abs(x), ay = Math.abs(y);
            y = 2 * ax * ay + ci; x = xx - yy + cr; xx = x * x; yy = y * y; n++;
          }
        } else {
          while (n < maxIter && xx + yy <= BAIL){
            y = 2 * x * y + ci; x = xx - yy + cr; xx = x * x; yy = y * y; n++;
          }
        }
        out[r * w + c] = n >= maxIter ? -1 : n + 1 - Math.log(Math.log(xx + yy) / 2) / LOG2;
      }
    }
    postMessage({ job, band, row0, rows, out }, [out.buffer]);
  };
}

/* ================= fractals: the page =================
   Content units are units of the complex plane: content (x, y) is the point
   RE0 + x + (IM0 − y)i, so the pan/zoom stage needs no special case. Zoom is free
   and unbounded; past about 10^14 the doubles run out of bits and pixels show. */
const RE0 = -2.75, IM0 = 1.6, FR_W = 4.1, FR_H = 3.2;
const PALETTES = {
  aurora: ["#020617", "#1E1B4B", "#4338CA", "#0EA5B7", "#5EEAD4", "#F0FDFA", "#F472B6", "#7C3AED", "#020617"],
  ember:  ["#050203", "#3F0A0A", "#9F1D0F", "#EA580C", "#FBBF24", "#FEF3C7", "#F59E0B", "#7C2D12", "#050203"],
  ocean:  ["#00040D", "#082F49", "#0369A1", "#22D3EE", "#ECFEFF", "#38BDF8", "#1E3A8A", "#00040D"],
  ink:    ["#000000", "#3A3A3A", "#BDBDBD", "#FFFFFF", "#9A9A9A", "#2A2A2A", "#000000"]
};
const FR = {
  kind: "mandel", palette: "aurora", iterRaw: "auto", jc: [-0.8, 0.156],
  lut: null, pool: [], queue: [], busy: 0, nextJob: 1, pz: null
};

function buildLut(){
  const stops = PALETTES[FR.palette].map(hexToRgb), N = 2048, lut = new Uint8ClampedArray(N * 3);
  for (let k = 0; k < N; k++){
    const t = k / N * (stops.length - 1), i = Math.floor(t), f = t - i;
    const a = stops[i], b = stops[Math.min(stops.length - 1, i + 1)];
    // smoothstep between stops keeps the bands soft
    const g = f * f * (3 - 2 * f);
    for (let ch = 0; ch < 3; ch++) lut[k * 3 + ch] = a[ch] + (b[ch] - a[ch]) * g;
  }
  FR.lut = lut;
}
function autoIter(s){
  const zoom = Math.max(1, s / 250);
  return Math.round(220 + 110 * Math.pow(Math.log10(zoom), 1.55));
}
function iterFor(s){
  const v = parseCount(FR.iterRaw);
  return Number.isFinite(v) && v > 0 ? v : autoIter(s);
}

/* ---- worker pool: bands of rows go to whichever worker is free ---- */
function ensurePool(){
  if (FR.pool.length) return;
  const n = clamp((navigator.hardwareConcurrency || 4) - 1, 2, 12);
  for (let k = 0; k < n; k++){
    const w = new Worker(workerUrl(fractalWorker));
    w.idle = true;
    w.onmessage = e => { w.idle = true; FR.busy--; onBand(e.data); pump(); };
    FR.pool.push(w);
  }
}
function pump(){
  for (const w of FR.pool){
    if (!w.idle) continue;
    let task;
    while ((task = FR.queue.shift()) && task.render.dead){ /* drop work for a superseded view */ }
    if (!task) return;
    w.idle = false; FR.busy++;
    w.postMessage(task.msg);
  }
}
const renders = new Map();
function killRender(r){ if (r){ r.dead = true; renders.delete(r.job); } }
function onBand(d){
  const r = renders.get(d.job);
  if (!r || r.dead) return;
  const px = r.img.data, lut = FR.lut, L = lut.length / 3, w = r.w;
  for (let k = 0; k < d.out.length; k++){
    const mu = d.out[k], o = (d.row0 * w + k) * 4;
    if (mu < 0){ px[o] = 0; px[o+1] = 0; px[o+2] = 0; }
    else {
      const t = (Math.sqrt(mu) * 0.115 + 0.62) % 1, li = Math.floor(t * L) * 3;
      px[o] = lut[li]; px[o+1] = lut[li+1]; px[o+2] = lut[li+2];
    }
    px[o+3] = 255;
  }
  r.left--;
  r.dirty = true;
  if (r.left === 0){ r.done = true; renders.delete(d.job); }
  if (!r.raf) r.raf = requestAnimationFrame(() => { r.raf = 0; flush(r); });
}
function flush(r){
  if (r.dead) return;
  r.ctx.putImageData(r.img, 0, 0);
  r.dirty = false;
  if (r.onUpdate) r.onUpdate(r);
  if (r.done && r.onDone) r.onDone(r);
}
/** Render a view: W × H device pixels, top-left complex point (re0, im0), step per pixel. */
function startRender(view, onUpdate, onDone){
  ensurePool();
  if (!FR.lut) buildLut();
  const job = FR.nextJob++;
  const cv = document.createElement("canvas");
  cv.width = view.W; cv.height = view.H;
  const ctx = cv.getContext("2d");
  const r = { job, w: view.W, h: view.H, canvas: cv, ctx, img: ctx.createImageData(view.W, view.H),
              left: 0, dead: false, done: false, view, onUpdate, onDone };
  const band = Math.max(4, Math.ceil(view.H / (FR.pool.length * 6)));
  const tasks = [];
  for (let row0 = 0; row0 < view.H; row0 += band){
    const rows = Math.min(band, view.H - row0);
    tasks.push({ render: r, msg: { job, band: tasks.length, kind: FR.kind, re0: view.re0, im0: view.im0, step: view.step,
      w: view.W, row0, rows, maxIter: view.maxIter, jr: FR.jc[0], ji: FR.jc[1] } });
  }
  // centre bands first, so the middle of the picture arrives soonest
  const mid = tasks.length / 2;
  tasks.sort((a, b) => Math.abs(a.msg.band - mid) - Math.abs(b.msg.band - mid));
  r.left = tasks.length;
  renders.set(job, r);
  FR.queue.push(...tasks);
  pump();
  return r;
}
function viewFor(pz, scale){
  const [Wc, Hc] = pz.size(), k = DPR() * (scale || 1);
  const W = Math.max(1, Math.round(Wc * k)), H = Math.max(1, Math.round(Hc * k));
  const step = 1 / (pz.s * k);
  return { W, H, step, re0: RE0 + (0.5 / k - pz.tx) / pz.s, im0: IM0 - (0.5 / k - pz.ty) / pz.s,
           s: pz.s, tx: pz.tx, ty: pz.ty, k, maxIter: iterFor(pz.s), key: FR.kind + FR.palette + FR.jc + FR.iterRaw };
}

/* Each stage keeps its own last render. Painting draws that picture moved and scaled
   to the current view at once, so dragging and zooming feel instant, then asks for a
   fresh render: a quick quarter-resolution pass, then the full one. */
function fractalSource(){
  return {
    kind: "fractal", w: FR_W, h: FR_H, pad: 0, free: true, minimap: false, maxScale: 1e18,
    title: { mandel: "Mandelbrot set", julia: "Julia set", ship: "Burning ship" }[FR.kind],
    meta: "",
    filename: FR.kind + "-" + Date.now() + ".png",
    paint(ctx, s, vis, pz){
      if (!pz) return;
      const st = pz.fr || (pz.fr = {});
      const key = FR.kind + FR.palette + FR.jc + FR.iterRaw;
      if (st.key !== key){ st.shown = null; st.key = key; }
      ctx.fillStyle = "#000";
      ctx.fillRect(vis.x0, vis.y0, vis.x1 - vis.x0, vis.y1 - vis.y0);
      for (const img of [st.low, st.shown]){
        if (!img || img.key !== key) continue;
        // the picture's content origin sits at −tx/s; redraw it under the current transform
        const v = img.view, kk = s / v.s;
        ctx.imageSmoothingEnabled = true;
        ctx.drawImage(img.canvas, -v.tx * kk, -v.ty * kk, v.W / v.k * kk, v.H / v.k * kk);
      }
      scheduleRender(pz);
    },
    home(pz){
      const [W, H] = pz.size();
      const width = FR.kind === "julia" ? 3.4 : FR.kind === "ship" ? 3.6 : 3.3;
      const cx = FR.kind === "mandel" ? -0.62 : FR.kind === "ship" ? -0.45 : 0;
      const cy = FR.kind === "ship" ? -0.5 : 0;
      pz.centerOn(cx - RE0, IM0 - cy, Math.min(W / width, H / (width * 0.78)));
    },
    zoomNote: s => "zoom " + (s / 250).toPrecision(3) + "×  ·  " + iterFor(s) + " iterations",
    png(){
      // render the current view again at twice the resolution, off screen
      const pz = viewer.open && viewer.src && viewer.src.kind === "fractal" ? viewer.pz : FR.pz;
      return new Promise(res => startRender(viewFor(pz, 2), null, r => res(r.canvas)));
    }
  };
}
function scheduleRender(pz){
  const st = pz.fr;
  const want = viewFor(pz, 1);
  const same = v => v && v.s === want.s && v.tx === want.tx && v.ty === want.ty && v.W === want.W && v.H === want.H && v.key === want.key;
  if (same(st.pendingView) || (st.shown && same(st.shown.view) && st.shown.done)) return;
  clearTimeout(st.timer);
  st.pendingView = want;
  st.timer = setTimeout(() => {
    killRender(st.active);
    killRender(st.activeLow);
    const key = want.key;
    const low = Object.assign({}, want, { W: Math.max(1, Math.round(want.W / 4)), H: Math.max(1, Math.round(want.H / 4)), step: want.step * 4, k: want.k / 4 });
    low.re0 = RE0 + (0.5 / low.k - want.tx) / want.s; low.im0 = IM0 - (0.5 / low.k - want.ty) / want.s;
    st.activeLow = startRender(low, null, r => {
      st.low = { canvas: r.canvas, view: low, key };
      pz.paint();
      st.active = startRender(want, r2 => {
        st.shown = { canvas: r2.canvas, view: want, key, done: r2.done };
        pz.paint();
      }, () => { st.pendingView = null; });
    });
  }, 70);
}

function setFractalKind(k){
  FR.kind = k;
  segSelect($("frKind"), "k", k);
  $("frTitle").textContent = { mandel: "Mandelbrot set", julia: "Julia set", ship: "Burning ship" }[k];
  FR.pz.setSource(fractalSource());
  updateFrNote();
}
function updateFrNote(){
  $("frNote").textContent = "zoom " + (FR.pz.s / 250).toPrecision(3) + "× · " + iterFor(FR.pz.s) + " iterations";
}
const FR_PLACES = {
  home: null,
  seahorse: [-0.7453, 0.1127, 0.0065],
  elephant: [0.2855, 0.0119, 0.022],
  spiral:   [-0.77568377, 0.13646737, 0.0023],
  mini:     [-1.7548776662, 0, 0.06]
};

function initFractal(){
  FR.pz = new PanZoom($("frStage"), {
    minimap: false,
    onProbe: () => { $("frHover").textContent = "Drag to pan · scroll to zoom · double-click to dive in" + (FR.kind === "mandel" ? " · click to pick a point for Julia" : ""); },
    onClick: (x, y) => {
      if (FR.kind !== "mandel") return;
      FR.jc = [RE0 + x, IM0 - y];
      toast("Point picked — switch to Julia to see its shape");
    },
    onPaint: () => updateFrNote()
  });
  segWire($("frKind"), "k", setFractalKind);
  segWire($("frPalette"), "p", p => { FR.palette = p; buildLut(); FR.pz.paint(); viewer.repaint(); });
  $("frIter").addEventListener("change", () => {
    const v = $("frIter").value.trim().toLowerCase();
    if (v !== "auto" && !(parseCount(v) > 0)){ $("frIter").classList.add("invalid"); return; }
    $("frIter").classList.remove("invalid");
    FR.iterRaw = v || "auto";
    FR.pz.paint(); viewer.repaint();
  });
  $("frIter").addEventListener("keydown", e => { if (e.key === "Enter") $("frIter").dispatchEvent(new Event("change")); });
  $("frPlaces").addEventListener("click", e => {
    const b = e.target.closest("button[data-place]");
    if (!b) return;
    const p = FR_PLACES[b.dataset.place];
    if (FR.kind !== "mandel") setFractalKind("mandel");
    if (!p){ FR.pz.home(); return; }
    const [W] = FR.pz.size();
    FR.pz.centerOn(p[0] - RE0, IM0 - p[1], W / p[2]);
  });
  $("frFull").addEventListener("click", () => viewer.show(fractalSource()));
  $("frSave").addEventListener("click", () => { const s = fractalSource(); savePng(s.png(), s.filename); });
}
