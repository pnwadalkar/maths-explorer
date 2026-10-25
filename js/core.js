"use strict";
/* ================= shared helpers ================= */
const $ = id => document.getElementById(id);
const fmt = n => n.toLocaleString("en-US");
/** Digit groups for a decimal string of any length, e.g. "-1000000" → "−1,000,000". */
const fmtDigits = s => (s[0] === "-" ? "−" : "") + s.replace("-", "").replace(/\B(?=(\d{3})+(?!\d))/g, ",");
const clamp = (v, lo, hi) => v < lo ? lo : v > hi ? hi : v;
const DPR = () => Math.min(window.devicePixelRatio || 1, 2);

function fmtMs(ms){
  if (ms < 1000) return Math.max(0, Math.round(ms)) + " ms";
  const s = ms / 1000;
  if (s < 60) return s.toFixed(s < 10 ? 2 : 1) + " s";
  return Math.floor(s / 60) + " min " + Math.round(s % 60) + " s";
}

const isDark = () => {
  const t = document.documentElement.getAttribute("data-theme");
  if (t === "dark") return true;
  if (t === "light") return false;
  return window.matchMedia && window.matchMedia("(prefers-color-scheme: dark)").matches;
};
const cssVar = name => getComputedStyle(document.documentElement).getPropertyValue(name).trim();

/** "1,000,000", "1e6", "2.5M", "10k", "2^20" → an integer, or NaN. Counts, not values: no sign. */
function parseCount(str){
  const s = String(str).trim().toLowerCase().replace(/[,_\s]/g, "");
  if (!s) return NaN;
  let m = s.match(/^(\d+(?:\.\d+)?)([kmb])?$/);
  if (m){
    const k = m[2] === "k" ? 1e3 : m[2] === "m" ? 1e6 : m[2] === "b" ? 1e9 : 1;
    return Math.round(parseFloat(m[1]) * k);
  }
  m = s.match(/^(\d+(?:\.\d+)?)e(\d+)$/);
  if (m) return Math.round(parseFloat(m[1]) * 10 ** parseInt(m[2], 10));
  m = s.match(/^(\d+)\^(\d+)$/);
  if (m) return Math.round(parseInt(m[1], 10) ** parseInt(m[2], 10));
  return NaN;
}

/** A whole-number expression to a BigInt: + − × ÷ ^ ! and brackets, e.g. "2^127 - 1" or "30!/(15!)^2". */
function parseBig(str){
  const s = String(str).replace(/[,_\s]/g, "").replace(/[×·]/g, "*").replace(/[−–]/g, "-").replace(/\*\*/g, "^");
  let p = 0;
  const fail = msg => { throw new Error(msg || "could not read “" + str + "” as a whole number"); };
  const peek = () => s[p];
  function expr(){
    let v = term();
    while (peek() === "+" || peek() === "-"){ const op = s[p++]; const r = term(); v = op === "+" ? v + r : v - r; }
    return v;
  }
  function term(){
    let v = unary();
    while (peek() === "*" || peek() === "/" || peek() === "%"){
      const op = s[p++]; const r = unary();
      if (op !== "*" && r === 0n) fail("division by zero");
      v = op === "*" ? v * r : op === "/" ? v / r : v % r;
    }
    return v;
  }
  // a power binds tighter than a sign, so −3^2 is −9, and powers stack to the right
  function unary(){
    if (peek() === "-"){ p++; return -unary(); }
    if (peek() === "+"){ p++; return unary(); }
    return power();
  }
  function power(){
    const b = postfix();
    if (peek() === "^"){ p++; const e = unary(); if (e < 0n) fail("negative powers are not whole numbers"); return b ** e; }
    return b;
  }
  function postfix(){
    let v = primary();
    while (peek() === "!"){
      p++;
      if (v < 0n) fail("factorial of a negative number");
      if (v > 200000n) fail("use the Big Numbers tool for factorials that large");
      let f = 1n; for (let k = 2n; k <= v; k++) f *= k; v = f;
    }
    return v;
  }
  function primary(){
    if (peek() === "("){ p++; const v = expr(); if (s[p++] !== ")") fail("a bracket is not closed"); return v; }
    const m = /^\d+/.exec(s.slice(p));
    if (!m) fail();
    p += m[0].length;
    return BigInt(m[0]);
  }
  const v = expr();
  if (p !== s.length) fail();
  return v;
}

/* ================= theme ================= */
const themeListeners = [];
let theme = "dark";
function applyTheme(t, remember){
  theme = t;
  if (t === "auto") document.documentElement.removeAttribute("data-theme");
  else document.documentElement.setAttribute("data-theme", t);
  $("themeDark").setAttribute("aria-pressed", String(t === "dark"));
  $("themeLight").setAttribute("aria-pressed", String(t === "light"));
  $("themeAuto").setAttribute("aria-pressed", String(t === "auto"));
  if (remember){ try { localStorage.setItem("maths-engine-theme", t); } catch (e) {} }
  themeListeners.forEach(fn => fn());
}

/* ================= toasts ================= */
function toast(msg, bad){
  const el = document.createElement("div");
  el.className = "toast" + (bad ? " bad" : "");
  el.textContent = msg;
  $("toasts").appendChild(el);
  setTimeout(() => { el.classList.add("out"); setTimeout(() => el.remove(), 320); }, bad ? 6500 : 4200);
}

/** Pressed-state helper for a group of toggle buttons sharing a data attribute. */
function segSelect(groupEl, attr, value){
  groupEl.querySelectorAll("button[data-" + attr + "]").forEach(b =>
    b.setAttribute("aria-pressed", String(b.dataset[attr] === value)));
}
function segWire(groupEl, attr, onPick){
  groupEl.addEventListener("click", e => {
    const b = e.target.closest("button[data-" + attr + "]");
    if (!b) return;
    segSelect(groupEl, attr, b.dataset[attr]);
    onPick(b.dataset[attr]);
  });
}

/* ================= background jobs =================
   Heavy arithmetic runs in a Web Worker so the page never freezes, however big the
   job. The worker is built from a function's source, so the app stays a handful of
   plain files that also open straight from disk. One job at a time per Job; a new
   run, or cancel(), terminates the old worker outright. */
const workerUrls = new Map();
function workerUrl(fn){
  let u = workerUrls.get(fn);
  if (!u){
    u = URL.createObjectURL(new Blob(["(" + fn.toString() + ")();"], { type: "text/javascript" }));
    workerUrls.set(fn, u);
  }
  return u;
}
class Job {
  constructor(fn){ this.fn = fn; this.worker = null; this.reject = null; }
  get busy(){ return !!this.worker; }
  run(msg, onProgress, transfer){
    this.cancel();
    const w = this.worker = new Worker(workerUrl(this.fn));
    return new Promise((resolve, reject) => {
      this.reject = reject;
      const end = () => {
        if (this.worker !== w) return;
        w.terminate(); this.worker = null; this.reject = null;
      };
      w.onmessage = e => {
        const d = e.data;
        if (d.type === "progress"){ if (onProgress) onProgress(d); return; }
        end();
        if (d.type === "error") reject(new Error(d.message));
        else resolve(d);
      };
      w.onerror = e => {
        e.preventDefault();
        end();
        reject(new Error(e.message || "the computation stopped unexpectedly — most likely it ran out of memory"));
      };
      w.postMessage(msg, transfer || []);
    });
  }
  cancel(){
    if (!this.worker) return;
    this.worker.terminate();
    this.worker = null;
    const r = this.reject;
    this.reject = null;
    if (r){ const err = new Error("cancelled"); err.cancelled = true; r(err); }
  }
}
/** Turn an engine error into a sentence a person can act on. */
function explainError(err){
  const m = String(err && err.message || err);
  if (/BigInt.*(size|too big|exceed)|Maximum BigInt/i.test(m))
    return "this needs a number larger than the browser's BigInt can hold (about a billion bits, roughly 323 million digits)";
  if (/memory|allocation|Invalid array length|Invalid string length|Array buffer allocation/i.test(m))
    return "the browser ran out of memory for a result this large";
  return m;
}

/** A progress line: an animated bar, a phase and a live elapsed clock. */
class Progress {
  constructor(el, textEl){ this.el = el; this.textEl = textEl; this.timer = 0; this.t0 = 0; this.msg = ""; this.frac = null; }
  start(msg){
    this.t0 = performance.now(); this.msg = msg; this.frac = null;
    this.el.hidden = false;
    clearInterval(this.timer);
    this.timer = setInterval(() => this.draw(), 100);
    this.draw();
  }
  set(msg, frac){ if (msg) this.msg = msg; this.frac = frac == null ? null : clamp(frac, 0, 1); this.draw(); }
  draw(){
    this.el.classList.toggle("indeterminate", this.frac == null);
    if (this.frac != null) this.el.style.setProperty("--p", (this.frac * 100).toFixed(1) + "%");
    this.textEl.textContent = this.msg + "  ·  " + fmtMs(performance.now() - this.t0);
  }
  stop(){ clearInterval(this.timer); this.el.hidden = true; return performance.now() - this.t0; }
}

/* ================= saving ================= */
let downloadsNs;           // undefined = not asked yet, null = unavailable
async function getDownloads(){
  if (downloadsNs !== undefined) return downloadsNs;
  try { downloadsNs = (window.claude && window.claude.use) ? await window.claude.use("downloads") : null; }
  catch (e) { downloadsNs = null; }
  return downloadsNs;
}
function canvasBlob(cv){ return new Promise(res => cv.toBlob(b => res(b), "image/png")); }
async function saveBlob(blob, filename, note){
  if (!blob){ toast("could not build the file", true); return; }
  const done = "Saved " + filename + (note ? " — " + note : "");
  const ns = await getDownloads();
  if (ns){
    try { await ns.save({ filename, data: blob }); toast(done); }
    catch (err){
      const code = err && err.code;
      toast(code === "declined" ? "Save cancelled" : code === "rate_limited" ? "A save prompt is already open"
        : "Saving is unavailable here", true);
    }
    return;
  }
  const url = URL.createObjectURL(blob);
  const a = document.createElement("a");
  a.href = url; a.download = filename;
  document.body.appendChild(a);
  a.click();
  a.remove();
  setTimeout(() => URL.revokeObjectURL(url), 15000);
  toast(done);
}
async function savePng(canvasOrPromise, filename, note){
  const cv = await canvasOrPromise;
  if (cv) await saveBlob(await canvasBlob(cv), filename, note);
}
function saveText(text, filename, mime, note){
  return saveBlob(new Blob([text], { type: mime + ";charset=utf-8" }), filename, note);
}
async function copyText(text, what){
  try { await navigator.clipboard.writeText(text); toast("Copied " + what); }
  catch (e) { toast("The clipboard refused — try Save .txt instead", true); }
}

/* ================= colour ================= */
function hslToRgb(h, s, l){
  h = ((h % 360) + 360) % 360 / 360;
  const f = (p, q, t) => {
    if (t < 0) t += 1;
    if (t > 1) t -= 1;
    if (t < 1/6) return p + (q - p) * 6 * t;
    if (t < 1/2) return q;
    if (t < 2/3) return p + (q - p) * (2/3 - t) * 6;
    return p;
  };
  if (s === 0){ const v = Math.round(l*255); return [v,v,v]; }
  const q = l < .5 ? l * (1 + s) : l + s - l * s;
  const p = 2 * l - q;
  return [f(p,q,h+1/3), f(p,q,h), f(p,q,h-1/3)].map(x => Math.round(x*255));
}
const rgbCss = c => "rgb(" + c[0] + "," + c[1] + "," + c[2] + ")";

/* Ten hues at even 36-degree steps, so the whole hue circle is covered; the yellows
   are darkened so no digit disappears against a light ground. */
const PALETTE = ["#E8384F","#ED7B16","#C9A227","#6CA62A","#12A06A",
                 "#0FA3B1","#2E6FD1","#5B4BD6","#9B3FC4","#D62E8A"];
const GREYS = Array.from({length:10}, (_, d) => {
  const v = Math.round(d * 255 / 9);
  return "#" + [v,v,v].map(x => x.toString(16).padStart(2, "0")).join("");
});
const hexToRgb = h => [parseInt(h.slice(1,3),16), parseInt(h.slice(3,5),16), parseInt(h.slice(5,7),16)];
const PAL_RGB = PALETTE.map(hexToRgb);
const GREY_RGB = GREYS.map(hexToRgb);

/** Frequency bars for the ten digits. */
function renderLegend(el, counts, colourOf){
  const total = counts.reduce((a, b) => a + b, 0) || 1;
  const peak = Math.max(1, ...counts);
  el.innerHTML = counts.map((c, d) =>
    '<div><span class="sw" style="background:' + colourOf(d) + '"></span>'
    + '<span class="d">' + d + '</span>'
    + '<span class="bar"><i style="width:' + (100 * c / peak).toFixed(1) + '%;background:' + colourOf(d) + '"></i></span>'
    + '<span class="c">' + fmt(c) + '</span>'
    + '<span class="pc">' + (100 * c / total).toFixed(2) + '%</span></div>').join("");
}
function digitCounts(str){
  const counts = new Array(10).fill(0);
  for (let i = 0; i < str.length; i++){
    const d = str.charCodeAt(i) - 48;
    if (d >= 0 && d <= 9) counts[d]++;
  }
  return counts;
}
function statTiles(el, rows){
  el.innerHTML = rows.map(([k, v, cls]) =>
    '<div><dt>' + k + '</dt><dd' + (cls ? ' class="' + cls + '"' : '') + '>' + v + '</dd></div>').join("");
}

/* ================= windowed digit stream =================
   Only the rows on screen exist in the DOM, so ten million digits scroll as easily
   as ten. Browsers stop honouring element heights somewhere past 15 million pixels,
   so past that the scrollbar is mapped proportionally onto the rows instead. */
const STREAM_MAX_H = 8e6;
class DigitStream {
  constructor(box, inner, note){
    this.box = box; this.inner = inner; this.note = note;
    this.digits = ""; this.cols = 50; this.rowH = 24; this.rows = 0; this.virtH = 0; this.hot = -1;
    box.addEventListener("scroll", () => this.render(), { passive: true });
    if (window.ResizeObserver){
      let lastW = 0;
      new ResizeObserver(() => {
        const w = box.clientWidth;
        if (!w || w === lastW) return;
        lastW = w;
        if (!this.digits.length) return;
        const at = Math.floor(this.topRow()) * this.cols;
        this.layout();
        if (at > 0) this.scrollToIndex(at);
      }).observe(box);
    }
  }
  set(digits){
    this.digits = digits; this.hot = -1;
    this.layout();
    this.box.scrollTop = 0;
    this.render();
  }
  measure(){
    const probe = document.createElement("span");
    probe.style.cssText = "position:absolute;visibility:hidden;white-space:pre;font-family:var(--font-mono);font-size:13px;letter-spacing:.05em";
    probe.textContent = "0".repeat(100);
    document.body.appendChild(probe);
    const charW = probe.getBoundingClientRect().width / 100 || 8;
    probe.remove();
    const posW = String(this.digits.length).length * 7.2;
    const avail = (this.box.clientWidth || 600) - 32 - 14 - posW - 12;
    const slots = Math.floor(avail / charW);
    // a row of c digits prints c + c/10 − 1 characters (a space between groups of ten)
    const c = Math.floor(((slots + 1) * 10 / 11) / 10) * 10;
    this.cols = Math.max(10, Math.min(100, c));
  }
  layout(){
    if (!this.digits.length){ this.inner.style.height = "0px"; this.inner.innerHTML = ""; return; }
    this.measure();
    this.rows = Math.ceil(this.digits.length / this.cols);
    this.virtH = Math.min(this.rows * this.rowH, STREAM_MAX_H);
    this.inner.style.height = this.virtH + "px";
    if (this.note) this.note.textContent = fmt(this.cols) + " per line · " + fmt(this.rows) + " lines";
    this.render();
  }
  /** The (fractional) row at the top of the window. */
  topRow(){
    const total = this.rows * this.rowH;
    if (total <= STREAM_MAX_H) return this.box.scrollTop / this.rowH;
    const span = Math.max(1, this.virtH - this.box.clientHeight);
    const visRows = this.box.clientHeight / this.rowH;
    return (this.box.scrollTop / span) * Math.max(0, this.rows - visRows);
  }
  render(){
    if (!this.digits.length) return;
    const f = this.topRow(), top = this.box.scrollTop;
    const first = Math.max(0, Math.floor(f) - 3);
    const last = Math.min(this.rows - 1, Math.ceil(f + this.box.clientHeight / this.rowH) + 3);
    const w = String(this.digits.length).length;
    let out = "";
    for (let r = first; r <= last; r++){
      const start = r * this.cols, end = Math.min(start + this.cols, this.digits.length);
      let s = "";
      for (let k = start; k < end; k += 10) s += (k > start ? " " : "") + this.digits.slice(k, Math.min(k + 10, end));
      const y = top + (r - f) * this.rowH;
      out += '<div class="srow' + (r === this.hot ? " hot" : "") + '" style="top:' + y.toFixed(1) + 'px">'
        + '<span class="spos" style="width:' + w + 'ch">' + (start + 1) + '</span><span class="sdig">' + s + '</span></div>';
    }
    this.inner.innerHTML = out;
  }
  scrollToIndex(i){
    const r = Math.floor(i / this.cols);
    this.hot = r;
    const total = this.rows * this.rowH;
    const want = r - this.box.clientHeight / this.rowH / 2 + 1;
    if (total <= STREAM_MAX_H) this.box.scrollTop = Math.max(0, want * this.rowH);
    else {
      const visRows = this.box.clientHeight / this.rowH;
      const span = Math.max(1, this.virtH - this.box.clientHeight);
      this.box.scrollTop = clamp(want / Math.max(1, this.rows - visRows), 0, 1) * span;
    }
    this.render();
  }
}

/* ================= pan / zoom stage =================
   A source describes a figure in its own content units:
     { w, h, paint(ctx, s, vis, pz), probe?(x, y), home?(pz), detail?(pz), maxScale?, free?, minimap? }
   paint draws with the content origin at (0,0) and s screen pixels per unit; vis is
   the visible rectangle in those screen pixels, so a figure only pays for what shows.
   The same source can be shown inline and in the full-screen viewer at once. */
class PanZoom {
  constructor(stage, opts){
    this.stage = stage;
    this.canvas = stage.querySelector("canvas");
    this.opts = opts || {};
    this.src = null; this.s = 1; this.tx = 0; this.ty = 0;
    this.raf = 0; this.thumb = null;
    if (this.opts.minimap !== false){
      this.mini = document.createElement("canvas");
      this.mini.className = "minimap";
      this.mini.hidden = true;
      stage.appendChild(this.mini);
    }
    stage.querySelectorAll(".stage-tools button").forEach(b => b.addEventListener("click", e => {
      e.stopPropagation();
      const z = b.dataset.z;
      if (z === "in") this.zoomBy(1.6);
      else if (z === "out") this.zoomBy(1 / 1.6);
      else this.home();
    }));
    this.gestures();
    /* A stage inside a hidden panel has no size, so a source set while hidden is
       homed the first time the stage is shown; after that a resize keeps the view. */
    this.needsHome = false;
    if (window.ResizeObserver){
      let last = "";
      new ResizeObserver(() => {
        if (!stage.clientWidth) return;
        const k = stage.clientWidth + "x" + stage.clientHeight;
        if (this.needsHome || !last){ last = k; this.needsHome = false; this.home(); return; }
        if (k === last){ this.paint(); return; }
        last = k;
        if (this.opts.refitOnResize) this.home(); else { this.clampPan(); this.paint(); }
      }).observe(stage);
    }
  }
  size(){ return [Math.max(1, this.stage.clientWidth), Math.max(1, this.stage.clientHeight)]; }
  setSource(src, keepView){
    this.src = src; this.thumb = null;
    if (keepView) { this.clampPan(); this.paint(); } else this.home();
  }
  fitScale(){
    const [W, H] = this.size(), pad = this.src.pad != null ? this.src.pad : 16;
    const f = Math.min((W - pad*2) / this.src.w, (H - pad*2) / this.src.h);
    return Number.isFinite(f) && f > 0 ? f : 1;
  }
  minScale(){ return this.fitScale() * 0.5; }
  maxScale(){ return this.src && this.src.maxScale ? this.src.maxScale : 64; }
  fit(){
    if (!this.src) return;
    const [W, H] = this.size();
    this.s = this.fitScale();
    this.tx = (W - this.src.w * this.s) / 2;
    this.ty = (H - this.src.h * this.s) / 2;
    this.paint();
  }
  home(){
    if (!this.src) return;
    if (!this.stage.clientWidth){ this.needsHome = true; return; }
    if (this.src.home) this.src.home(this); else this.fit();
  }
  /** Put content point (x, y) at the centre of the stage at scale s. */
  centerOn(x, y, s){
    const [W, H] = this.size();
    if (s != null) this.s = clamp(s, this.minScale(), this.maxScale());
    this.tx = W / 2 - x * this.s;
    this.ty = H / 2 - y * this.s;
    this.clampPan(); this.paint();
  }
  /** Show content point (x, y) at the stage's top-left corner, at scale s. */
  cornerOn(x, y, s){
    this.s = clamp(s, this.minScale(), this.maxScale());
    this.tx = -x * this.s; this.ty = -y * this.s;
    this.clampPan(); this.paint();
  }
  zoomTo(s, cx, cy){
    if (!this.src) return;
    const [W, H] = this.size();
    if (cx == null){ cx = W / 2; cy = H / 2; }
    const ns = clamp(s, this.minScale(), this.maxScale());
    const k = ns / this.s;
    this.tx = cx - (cx - this.tx) * k;
    this.ty = cy - (cy - this.ty) * k;
    this.s = ns;
    this.clampPan(); this.paint();
  }
  zoomBy(f, cx, cy){ this.zoomTo(this.s * f, cx, cy); }
  panBy(dx, dy){ this.tx += dx; this.ty += dy; this.clampPan(); this.paint(); }
  clampPan(){
    if (!this.src || this.src.free) return;
    const [W, H] = this.size(), w = this.src.w * this.s, h = this.src.h * this.s, m = 48;
    this.tx = w <= W ? (W - w) / 2 : clamp(this.tx, W - w - m, m);
    this.ty = h <= H ? (H - h) / 2 : clamp(this.ty, H - h - m, m);
  }
  /** Content coordinates under a client point. */
  contentAt(clientX, clientY){
    const r = this.stage.getBoundingClientRect();
    return [(clientX - r.left - this.tx) / this.s, (clientY - r.top - this.ty) / this.s];
  }
  /** The visible content rectangle. */
  visibleContent(){
    const [W, H] = this.size();
    return { x0: -this.tx / this.s, y0: -this.ty / this.s, x1: (W - this.tx) / this.s, y1: (H - this.ty) / this.s };
  }
  paint(){
    if (this.raf) return;
    this.raf = requestAnimationFrame(() => { this.raf = 0; this.paintNow(); });
  }
  paintNow(){
    if (!this.src || !this.stage.clientWidth) return;
    const [W, H] = this.size(), dpr = DPR(), cv = this.canvas;
    const pw = Math.round(W * dpr), ph = Math.round(H * dpr);
    if (cv.width !== pw || cv.height !== ph){ cv.width = pw; cv.height = ph; }
    cv.style.width = W + "px"; cv.style.height = H + "px";
    const ctx = cv.getContext("2d");
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.clearRect(0, 0, W, H);
    const x = Math.round(this.tx), y = Math.round(this.ty);
    ctx.save();
    ctx.translate(x, y);
    this.src.paint(ctx, this.s, { x0: -x, y0: -y, x1: -x + W, y1: -y + H }, this);
    ctx.restore();
    this.paintMini();
    if (this.opts.onPaint) this.opts.onPaint(this);
  }
  paintMini(){
    const mini = this.mini;
    if (!mini) return;
    const [W, H] = this.size(), src = this.src;
    const zoomed = src.w * this.s > W + 2 || src.h * this.s > H + 2;
    if (!zoomed || src.minimap === false || W < 360){ mini.hidden = true; return; }
    const side = 132, k = side / Math.max(src.w, src.h);
    const mw = Math.max(24, Math.round(src.w * k)), mh = Math.max(24, Math.round(src.h * k));
    const dpr = DPR();
    if (!this.thumb || this.thumb.dark !== isDark()){
      // the overview is painted once per source and theme, then only the window moves
      const t = document.createElement("canvas");
      t.width = Math.round(mw * dpr); t.height = Math.round(mh * dpr);
      const tctx = t.getContext("2d");
      tctx.setTransform(dpr, 0, 0, dpr, 0, 0);
      src.paint(tctx, mw / src.w, null, null);
      t.dark = isDark();
      this.thumb = t;
    }
    mini.hidden = false;
    mini.width = Math.round(mw * dpr); mini.height = Math.round(mh * dpr);
    mini.style.width = mw + "px"; mini.style.height = mh + "px";
    const ctx = mini.getContext("2d");
    ctx.setTransform(1, 0, 0, 1, 0, 0);
    ctx.drawImage(this.thumb, 0, 0);
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    const v = this.visibleContent(), kx = mw / src.w, ky = mh / src.h;
    const rx = clamp(v.x0 * kx, 0, mw), ry = clamp(v.y0 * ky, 0, mh);
    const rw = clamp(v.x1 * kx, 0, mw) - rx, rh = clamp(v.y1 * ky, 0, mh) - ry;
    ctx.fillStyle = "rgba(0,0,0,.35)";
    ctx.fillRect(0, 0, mw, ry); ctx.fillRect(0, ry + rh, mw, mh - ry - rh);
    ctx.fillRect(0, ry, rx, rh); ctx.fillRect(rx + rw, ry, mw - rx - rw, rh);
    ctx.strokeStyle = "#FFD45E"; ctx.lineWidth = 1.5;
    ctx.strokeRect(rx + .75, ry + .75, Math.max(2, rw - 1.5), Math.max(2, rh - 1.5));
  }
  gestures(){
    const st = this.stage, pts = new Map();
    let drag = null, pinch = null, moved = false;
    st.addEventListener("pointerdown", e => {
      if (e.target.closest(".stage-tools")) return;
      st.setPointerCapture(e.pointerId);
      pts.set(e.pointerId, [e.clientX, e.clientY]);
      moved = false;
      if (pts.size === 1){ drag = { x: e.clientX, y: e.clientY }; }
      else if (pts.size === 2){
        const [a, b] = [...pts.values()];
        pinch = { d: Math.hypot(a[0]-b[0], a[1]-b[1]), s: this.s, mx: (a[0]+b[0])/2, my: (a[1]+b[1])/2 };
        drag = null;
      }
    });
    st.addEventListener("pointermove", e => {
      if (pts.has(e.pointerId)) pts.set(e.pointerId, [e.clientX, e.clientY]);
      if (pinch && pts.size >= 2){
        const [a, b] = [...pts.values()];
        const d = Math.hypot(a[0]-b[0], a[1]-b[1]);
        const r = st.getBoundingClientRect();
        const mx = (a[0]+b[0])/2, my = (a[1]+b[1])/2;
        this.tx += mx - pinch.mx; this.ty += my - pinch.my;
        pinch.mx = mx; pinch.my = my;
        this.zoomTo(pinch.s * d / Math.max(1, pinch.d), mx - r.left, my - r.top);
        moved = true;
        return;
      }
      if (drag){
        const dx = e.clientX - drag.x, dy = e.clientY - drag.y;
        if (!moved && Math.abs(dx) + Math.abs(dy) < 4) return;
        if (!moved){ moved = true; st.classList.add("dragging"); }
        drag.x = e.clientX; drag.y = e.clientY;
        this.panBy(dx, dy);
        return;
      }
      if (e.pointerType === "mouse" && this.src && this.opts.onProbe){
        const [x, y] = this.contentAt(e.clientX, e.clientY);
        this.opts.onProbe(this.src.probe ? this.src.probe(x, y) : "", x, y);
      }
    });
    const end = e => {
      const wasTap = pts.size === 1 && !moved && drag;
      pts.delete(e.pointerId);
      try { st.releasePointerCapture(e.pointerId); } catch (err) {}
      if (pts.size < 2) pinch = null;
      if (pts.size === 1){ const [p] = pts.values(); drag = { x: p[0], y: p[1] }; }
      if (pts.size === 0){
        drag = null;
        st.classList.remove("dragging");
        if (wasTap && e.type === "pointerup" && this.opts.onClick && this.src){
          const [x, y] = this.contentAt(e.clientX, e.clientY);
          this.opts.onClick(x, y, e);
        }
      }
    };
    st.addEventListener("pointerup", end);
    st.addEventListener("pointercancel", end);
    st.addEventListener("pointerleave", e => { if (!pts.size && this.opts.onLeave) this.opts.onLeave(e); });
    st.addEventListener("wheel", e => {
      if (!this.src) return;
      // Inline figures leave the page free to scroll; Ctrl/⌘ (or a trackpad pinch,
      // which arrives as Ctrl+wheel) zooms. The full-screen viewer always zooms.
      if (!this.opts.wheelAlways && !e.ctrlKey && !e.metaKey){ this.nudge(); return; }
      e.preventDefault();
      const r = st.getBoundingClientRect();
      const dy = e.deltaMode === 1 ? e.deltaY * 16 : e.deltaY;
      this.zoomBy(Math.exp(-clamp(dy, -120, 120) * 0.0022), e.clientX - r.left, e.clientY - r.top);
    }, { passive: false });
    st.addEventListener("dblclick", e => {
      if (e.target.closest(".stage-tools") || !this.src) return;
      const r = st.getBoundingClientRect();
      this.zoomBy(e.shiftKey ? 1 / 2.2 : 2.2, e.clientX - r.left, e.clientY - r.top);
    });
  }
  /** A one-time reminder that inline zoom wants a modifier, so scrolling never feels stuck. */
  nudge(){
    if (PanZoom.nudged) return;
    PanZoom.nudged = true;
    toast("Hold Ctrl (⌘ on a Mac) while scrolling to zoom — or pinch, or use the + / − buttons");
  }
}

/* ================= full-screen viewer ================= */
const viewer = {
  open: false, src: null, pz: null,
  init(){
    this.pz = new PanZoom($("viewerStage"), {
      wheelAlways: true, refitOnResize: false,
      onProbe: txt => { $("viewerProbe").textContent = txt || "Drag to pan · scroll or +/− to zoom · 0 to fit · Esc to close"; },
      onPaint: pz => {
        const src = this.src;
        if (!src) return;
        $("viewerZoomNote").textContent = src.zoomNote ? src.zoomNote(pz.s) : (pz.s < 1 ? pz.s.toFixed(3) : pz.s.toFixed(1)) + " px per unit";
      }
    });
    $("viewerClose").addEventListener("click", () => this.close());
    $("viewerFit").addEventListener("click", () => this.pz.home());
    $("viewerIn").addEventListener("click", () => this.pz.zoomBy(1.4));
    $("viewerOut").addEventListener("click", () => this.pz.zoomBy(1 / 1.4));
    $("viewerOne").addEventListener("click", () => {
      const src = this.src;
      if (!src) return;
      if (src.detail) src.detail(this.pz); else this.pz.zoomBy(4);
    });
    $("viewerSave").addEventListener("click", () => {
      const src = this.src;
      if (src && src.png) savePng(src.png(), src.filename, src.pngNote ? src.pngNote() : null);
    });
    document.addEventListener("keydown", e => {
      if (!this.open) return;
      const pz = this.pz;
      if (e.key === "Escape"){ this.close(); return; }
      if (e.key === "+" || e.key === "=") pz.zoomBy(1.35);
      else if (e.key === "-" || e.key === "_") pz.zoomBy(1 / 1.35);
      else if (e.key === "0") pz.home();
      else if (e.key === "ArrowLeft") pz.panBy(80, 0);
      else if (e.key === "ArrowRight") pz.panBy(-80, 0);
      else if (e.key === "ArrowUp") pz.panBy(0, 80);
      else if (e.key === "ArrowDown") pz.panBy(0, -80);
      else return;
      e.preventDefault();
    });
    document.addEventListener("fullscreenchange", () => {
      if (this.open && !document.fullscreenElement) this.close();
    });
  },
  show(src){
    if (!src) return;
    this.src = src; this.open = true;
    $("viewerTitle").textContent = src.title || "Figure";
    $("viewerMeta").textContent = src.meta || "";
    $("viewerOne").hidden = !src.detail;
    $("viewerSave").hidden = !src.png;
    $("viewer").hidden = false;
    document.body.style.overflow = "hidden";
    const el = $("viewer");
    if (el.requestFullscreen) el.requestFullscreen().catch(() => {});
    // the stage only has its size once the overlay is laid out
    requestAnimationFrame(() => requestAnimationFrame(() => this.pz.setSource(src)));
  },
  close(){
    if (!this.open) return;
    this.open = false; this.src = null;
    $("viewer").hidden = true;
    document.body.style.overflow = "";
    if (document.fullscreenElement && document.exitFullscreen) document.exitFullscreen().catch(() => {});
  },
  repaint(){ if (this.open) { this.pz.thumb = null; this.pz.paint(); } }
};
