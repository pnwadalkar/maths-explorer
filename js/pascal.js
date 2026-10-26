"use strict";
/* ================= Pascal's triangle =================
   Row r holds C(r, 0) … C(r, r). Cells sit on a square grid with each row shifted
   half a cell, so R rows make a figure R wide and R tall in content units. Colours
   come from remainders, which follow the same add-the-two-above rule, so thousands
   of rows cost a few megabytes; exact values are only worked out for cells on screen. */
const PAS_MAX = 2048;
const PAS = { R: 16, mode: "2", hl: "none", lf: null, res: null, resMod: 0, img: null, imgKey: "", vals: new Map(), pz: null };
const PAS_RES = [PALETTE[6], PALETTE[0], PALETTE[4], PALETTE[1], PALETTE[8], PALETTE[5]];
const PAS_RES_RGB = PAS_RES.map(hexToRgb);
const PAS_MODES = { "2": "odd numbers lit", "3": "coloured by remainder after dividing by 3",
  "5": "coloured by remainder after dividing by 5", "7": "coloured by remainder after dividing by 7", size: "coloured by size" };

const pasRowStart = r => r * (r + 1) / 2;
/** log10 C(r, k), from a table of log10 r! — the size of a number too big to write out. */
const pasLog = (r, k) => PAS.lf[r] - PAS.lf[k] - PAS.lf[r - k];
const pasDigits = (r, k) => Math.floor(pasLog(r, k) + 1e-9) + 1;

function pasBuild(){
  const R = PAS.R, lf = new Float64Array(R + 1);
  for (let k = 2; k <= R; k++) lf[k] = lf[k - 1] + Math.log10(k);
  PAS.lf = lf; PAS.res = null; PAS.resMod = 0; PAS.img = null; PAS.vals.clear();
}
function pasResidues(m){
  if (PAS.res && PAS.resMod === m) return PAS.res;
  const R = PAS.R, res = new Uint8Array(pasRowStart(R));
  for (let r = 0; r < R; r++){
    const o = pasRowStart(r), p = o - r;
    res[o] = res[o + r] = 1 % m;
    for (let k = 1; k < r; k++) res[o + k] = (res[p + k - 1] + res[p + k]) % m;
  }
  PAS.res = res; PAS.resMod = m;
  return res;
}
/** The exact value of C(r, k) as a decimal string. */
function pasValue(r, k){
  const key = r * PAS_MAX + k;
  let v = PAS.vals.get(key);
  if (v === undefined){
    const j = Math.min(k, r - k);
    let b = 1n;
    for (let i = 1; i <= j; i++) b = b * BigInt(r - j + i) / BigInt(i);
    v = b.toString();
    if (PAS.vals.size > 20000) PAS.vals.clear();
    PAS.vals.set(key, v);
  }
  return v;
}

/* One hue, light to dark, for size: small numbers recede, big ones stand out. */
const PAS_SEQ = { light: [[221, 222, 251], [43, 43, 168]], dark: [[30, 33, 64], [185, 185, 255]] };
function pasSizeRgb(t, dark){
  const [a, b] = dark ? PAS_SEQ.dark : PAS_SEQ.light;
  return [0, 1, 2].map(i => Math.round(a[i] + (b[i] - a[i]) * t));
}
function pasColours(dark){
  return { dim: dark ? [28, 35, 55] : [227, 230, 239], ink: dark ? "#0A0B1A" : "#FFFFFF",
           inkDim: dark ? "#98A0B6" : "#5B6275", ring: "#F5C84B" };
}
/** [fill rgb, text colour] for one cell. */
function pasCell(r, k, dark, col, maxLog){
  if (PAS.mode === "size"){
    const t = maxLog > 0 ? pasLog(r, k) / maxLog : 0;
    return [pasSizeRgb(t, dark), (dark ? t < 0.55 : t > 0.45) ? "#F4F5FB" : "#10131C"];
  }
  const v = PAS.res[pasRowStart(r) + k];
  return v === 0 ? [col.dim, col.inkDim] : [PAS_RES_RGB[v - 1], col.ink];
}
const pasMaxLog = () => PAS.R > 1 ? pasLog(PAS.R - 1, (PAS.R - 1) >> 1) : 0;
const pasLit = (r, k) => PAS.hl === "count" ? r >= 2 && (k === 1 || k === r - 1)
  : PAS.hl === "tri" ? r >= 2 && (k === 2 || k === r - 2) : false;

/* Zoomed out, the whole triangle is one picture made once per setting and theme. */
function pasImage(dark){
  const key = PAS.R + PAS.mode + dark;
  if (PAS.img && PAS.imgKey === key) return PAS.img;
  const R = PAS.R, k = R <= 1024 ? 2 : 1, col = pasColours(dark), maxLog = pasMaxLog();
  const cv = document.createElement("canvas");
  cv.width = cv.height = R * k;
  const ctx = cv.getContext("2d"), img = ctx.createImageData(R * k, R * k), d = img.data;
  for (let r = 0; r < R; r++){
    const x0 = Math.round((R - 1 - r) / 2 * k);
    for (let c = 0; c <= r; c++){
      const [rgb] = pasCell(r, c, dark, col, maxLog);
      for (let dy = 0; dy < k; dy++) for (let dx = 0; dx < k; dx++){
        const i = ((r * k + dy) * R * k + x0 + c * k + dx) * 4;
        d[i] = rgb[0]; d[i + 1] = rgb[1]; d[i + 2] = rgb[2]; d[i + 3] = 255;
      }
    }
  }
  ctx.putImageData(img, 0, 0);
  PAS.img = cv; PAS.imgKey = key;
  return cv;
}

function pascalSource(){
  const R = PAS.R;
  return {
    kind: "pascal", w: R, h: R, pad: 12, maxScale: 160,
    title: "Pascal’s triangle, " + fmt(R) + " rows",
    meta: PAS_MODES[PAS.mode],
    filename: "pascal-" + R + "-rows.png",
    paint(ctx, s, vis){
      const dark = isDark(), col = pasColours(dark);
      if (PAS.mode !== "size") pasResidues(+PAS.mode);
      if (s < 3){
        ctx.imageSmoothingEnabled = s < 1;
        ctx.drawImage(pasImage(dark), 0, 0, R * s, R * s);
        if (PAS.hl !== "none" && R > 2){
          // the highlighted diagonals are straight lines through the cell centres
          const k = PAS.hl === "count" ? 1 : 2, top = 2, bot = R - 1;
          const left = r => ((R - 1 - r) / 2 + k + .5) * s, right = r => ((R - 1 + r) / 2 - k + .5) * s;
          ctx.strokeStyle = col.ring; ctx.lineWidth = 2; ctx.lineCap = "round";
          ctx.beginPath();
          ctx.moveTo(left(top), (top + .5) * s); ctx.lineTo(left(bot), (bot + .5) * s);
          ctx.moveTo(right(top), (top + .5) * s); ctx.lineTo(right(bot), (bot + .5) * s);
          ctx.stroke();
        }
        return;
      }
      const maxLog = pasMaxLog();
      const y0 = vis ? vis.y0 : 0, y1 = vis ? vis.y1 : R * s;
      const r0 = Math.max(0, Math.floor(y0 / s)), r1 = Math.min(R - 1, Math.floor(y1 / s));
      const gap = s >= 6 ? Math.max(1, s * 0.07) : 0, rr = Math.min(8, s * 0.2);
      const maxLen = Math.floor(s * 0.76 / (0.62 * 7));
      ctx.textAlign = "center"; ctx.textBaseline = "middle";
      for (let r = r0; r <= r1; r++){
        const off = (R - 1 - r) / 2;
        const c0 = vis ? Math.max(0, Math.floor(vis.x0 / s - off)) : 0;
        const c1 = vis ? Math.min(r, Math.floor(vis.x1 / s - off)) : r;
        for (let c = c0; c <= c1; c++){
          const x = (off + c) * s, y = r * s;
          const [rgb, ink] = pasCell(r, c, dark, col, maxLog);
          ctx.fillStyle = rgbCss(rgb);
          if (gap){
            ctx.beginPath();
            if (ctx.roundRect) ctx.roundRect(x + gap, y + gap, s - gap * 2, s - gap * 2, rr);
            else ctx.rect(x + gap, y + gap, s - gap * 2, s - gap * 2);
            ctx.fill();
          } else ctx.fillRect(x, y, s, s);
          if (pasLit(r, c)){
            ctx.strokeStyle = col.ring; ctx.lineWidth = Math.max(1.5, Math.min(3, s / 12));
            ctx.strokeRect(x + gap + .75, y + gap + .75, s - gap * 2 - 1.5, s - gap * 2 - 1.5);
          }
          // write the number whenever it fits at a readable size
          if (s >= 12 && pasDigits(r, c) <= maxLen + 1){
            const txt = pasValue(r, c), f = Math.min(s * 0.4, s * 0.76 / (txt.length * 0.62));
            if (f >= 7){
              ctx.font = "500 " + f.toFixed(1) + "px \"JetBrains Mono\", ui-monospace, monospace";
              ctx.fillStyle = ink;
              ctx.fillText(txt, x + s / 2, y + s / 2 + s * 0.02);
            }
          }
        }
      }
    },
    probe(x, y){
      const r = Math.floor(y);
      if (r < 0 || r >= R) return "";
      const c = Math.floor(x - (R - 1 - r) / 2);
      if (c < 0 || c > r) return "";
      const dg = pasDigits(r, c);
      let s = "Row " + r + ", place " + c + ":  " + (dg <= 60 ? fmtDigits(pasValue(r, c)) : "a number " + fmt(dg) + " digits long");
      if (c > 0 && c < r && dg <= 24) s += "  =  " + fmtDigits(pasValue(r - 1, c - 1)) + " + " + fmtDigits(pasValue(r - 1, c)) + " (the two above)";
      return s;
    },
    detail(pz){ const v = pz.visibleContent(); pz.centerOn((v.x0 + v.x1) / 2, (v.y0 + v.y1) / 2, 48); },
    zoomNote: s => (s < 1 ? s.toFixed(3) : s.toFixed(1)) + " px per number",
    png(){
      const s = clamp(Math.floor(2400 / R), 1, 48), pad = 16;
      const cv = document.createElement("canvas");
      cv.width = cv.height = R * s + pad * 2;
      const ctx = cv.getContext("2d");
      ctx.fillStyle = cssVar("--surface-solid") || "#FFFFFF";
      ctx.fillRect(0, 0, cv.width, cv.height);
      ctx.translate(pad, pad);
      this.paint(ctx, s, null);
      return cv;
    }
  };
}

function renderPascalKey(){
  const dark = isDark(), col = pasColours(dark), m = PAS.mode;
  const sw = c => '<span class="sw" style="background:' + c + '"></span>';
  let html;
  if (m === "size"){
    html = '<div class="ramp"><span>small</span><i style="background:linear-gradient(90deg,' + rgbCss(pasSizeRgb(0, dark)) + ","
      + rgbCss(pasSizeRgb(1, dark)) + ')"></i><span>huge</span></div>';
  } else if (m === "2"){
    html = "<div>" + sw(PAS_RES[0]) + "odd</div><div>" + sw(rgbCss(col.dim)) + "even</div>";
  } else {
    html = "<div>" + sw(rgbCss(col.dim)) + "divisible by " + m + "</div>"
      + Array.from({ length: +m - 1 }, (_, i) => "<div>" + sw(PAS_RES[i]) + "remainder " + (i + 1) + "</div>").join("");
  }
  $("pasKey").innerHTML = html;
}

function renderPascalStats(){
  const R = PAS.R, last = R - 1;
  let odd = 0;
  // row r has 2^(number of 1s in r written in binary) odd numbers
  for (let r = 0; r < R; r++){ let b = 0, x = r; while (x){ b += x & 1; x >>= 1; } odd += 2 ** b; }
  const total = pasRowStart(R), dg = pasDigits(last, last >> 1);
  statTiles($("pasStats"), [
    ["Rows", fmt(R), "big"],
    ["Numbers", fmt(total)],
    ["Biggest number", (dg <= 18 ? fmtDigits(pasValue(last, last >> 1)) : fmt(dg) + " digits") + "<small>middle of the last row</small>"],
    ["Odd numbers", fmt(odd) + "<small>" + (100 * odd / total).toFixed(1) + "% of them</small>"],
    ["Last row adds up to", (last <= 60 ? fmtDigits((2n ** BigInt(last)).toString()) : "2<sup>" + fmt(last) + "</sup>")
      + "<small>2 multiplied by itself " + fmt(last) + " times</small>"]
  ]);
}

function buildPascal(){
  const R = parseCount($("pasRows").value);
  if (!(R >= 1)){ $("pasRows").classList.add("invalid"); toast("Type how many rows you want, like 16 or 512", true); return; }
  if (R > PAS_MAX){ $("pasRows").classList.add("invalid"); toast("Pascal’s triangle goes up to " + fmt(PAS_MAX) + " rows here", true); return; }
  $("pasRows").classList.remove("invalid");
  $("pasRows").value = fmt(R);
  PAS.R = R;
  pasBuild();
  renderPascalStats();
  renderPascalKey();
  $("pasNote").textContent = fmt(R) + " rows · " + PAS_MODES[PAS.mode];
  PAS.pz.setSource(pascalSource());
}
function repaintPascal(){
  renderPascalKey();
  $("pasNote").textContent = fmt(PAS.R) + " rows · " + PAS_MODES[PAS.mode];
  PAS.pz.setSource(pascalSource(), true);
  viewer.repaint();
}

function initPascal(){
  PAS.pz = new PanZoom($("pasStage"), {
    onProbe: txt => { $("pasHover").textContent = txt || "Point at a number to see which two numbers above add up to it."; }
  });
  $("pasBuild").addEventListener("click", buildPascal);
  $("pasRows").addEventListener("keydown", e => { if (e.key === "Enter") buildPascal(); });
  $("pasPresets").addEventListener("click", e => {
    const b = e.target.closest("button[data-n]");
    if (!b) return;
    $("pasRows").value = b.dataset.n;
    buildPascal();
  });
  segWire($("pasColour"), "m", m => { PAS.mode = m; repaintPascal(); });
  segWire($("pasHl"), "h", h => { PAS.hl = h; repaintPascal(); });
  $("pasFull").addEventListener("click", () => viewer.show(pascalSource()));
  $("pasSave").addEventListener("click", () => { const s = pascalSource(); savePng(s.png(), s.filename); });
  themeListeners.push(() => { if (PAS.lf){ renderPascalKey(); PAS.pz.paint(); } });
}
