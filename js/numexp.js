"use strict";
/* ================= number explorer =================
   Everything here works on whole numbers up to 10^15, where plain JavaScript numbers
   are still exact, so every fact is worked out on the page at once. */
const NX_MAX = 1e15;
const NX = { n: 0, seq: null, exact: null, peakAt: 0, hover: -1, geom: null };
const NX_SURPRISE = [6, 28, 153, 370, 495, 496, 1001, 1729, 2047, 5040, 6174, 8128, 8191, 9474, 27, 97, 142857, 65537, 524287, 3628800, 1000000007];

function nxModPow(b, e, m){
  let r = 1n;
  b %= m;
  while (e > 0n){ if (e & 1n) r = r * b % m; b = b * b % m; e >>= 1n; }
  return r;
}
/** Exact for every n below 3.3 × 10^24, far past what this tool accepts. */
function nxIsPrime(n){
  if (n < 2) return false;
  const bases = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];
  for (const p of bases){ if (n === p) return true; if (n % p === 0) return false; }
  const N = BigInt(n);
  let d = N - 1n, s = 0;
  while (!(d & 1n)){ d >>= 1n; s++; }
  outer: for (const a of bases){
    let x = nxModPow(BigInt(a), d, N);
    if (x === 1n || x === N - 1n) continue;
    for (let i = 1; i < s; i++){ x = x * x % N; if (x === N - 1n) continue outer; }
    return false;
  }
  return true;
}
/** [[prime, power], …] in increasing order. */
function nxFactor(n){
  const out = [];
  let rest = n;
  const take = p => { let e = 0; while (rest % p === 0){ rest /= p; e++; } if (e) out.push([p, e]); return e > 0; };
  take(2); take(3);
  let done = rest === 1 || nxIsPrime(rest);
  for (let p = 5; !done && p * p <= rest; p += 6){
    const a = take(p), b = take(p + 2);
    if (a || b) done = rest === 1 || nxIsPrime(rest);
  }
  if (rest > 1) out.push([rest, 1]);
  return out;
}
function nxDivisors(fs){
  let ds = [1];
  for (const [p, e] of fs){
    const next = [];
    for (const d of ds){ let v = d; for (let i = 0; i <= e; i++){ next.push(v); v *= p; } }
    ds = next;
  }
  return ds.sort((a, b) => a - b);
}

/* ---- writing it other ways ---- */
const NX_ONES = ["zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine", "ten", "eleven", "twelve",
  "thirteen", "fourteen", "fifteen", "sixteen", "seventeen", "eighteen", "nineteen"];
const NX_TENS = ["", "", "twenty", "thirty", "forty", "fifty", "sixty", "seventy", "eighty", "ninety"];
const NX_SCALES = ["", " thousand", " million", " billion", " trillion", " quadrillion"];
function nxUnder100(n){ return n < 20 ? NX_ONES[n] : NX_TENS[Math.floor(n / 10)] + (n % 10 ? "-" + NX_ONES[n % 10] : ""); }
function nxUnder1000(n){
  const h = Math.floor(n / 100), r = n % 100;
  return (h ? NX_ONES[h] + " hundred" + (r ? " and " : "") : "") + (r || !h ? nxUnder100(r) : "");
}
function nxWords(n){
  if (n === 0) return "zero";
  const groups = [];
  for (let x = n; x > 0; x = Math.floor(x / 1000)) groups.push(x % 1000);
  const parts = [];
  for (let i = groups.length - 1; i >= 0; i--){
    if (!groups[i]) continue;
    // "one thousand and five": a last group under 100 joins with "and"
    const and = i === 0 && groups.length > 1 && groups[0] < 100 ? "and " : "";
    parts.push(and + nxUnder1000(groups[i]) + NX_SCALES[i]);
  }
  return parts.join(", ").replace(/, and /g, " and ");
}
function nxRoman(n){
  if (n > 3999) return null;
  const marks = [[1000, "M"], [900, "CM"], [500, "D"], [400, "CD"], [100, "C"], [90, "XC"], [50, "L"], [40, "XL"], [10, "X"], [9, "IX"], [5, "V"], [4, "IV"], [1, "I"]];
  let s = "";
  for (const [v, m] of marks) while (n >= v){ s += m; n -= v; }
  return s;
}
const nxGroup = (s, k) => s.replace(new RegExp("\\B(?=(.{" + k + "})+$)", "g"), " ");

/* ---- what kind of number is it? ---- */
const NX_FIB = (() => { const f = [1, 2]; while (f[f.length - 1] <= NX_MAX) f.push(f[f.length - 1] + f[f.length - 2]); return f; })();
function nxKinds(n, fs, divSum){
  const str = String(n), len = str.length, digits = [...str].map(Number);
  const dsum = digits.reduce((a, b) => a + b, 0);
  const kinds = [];
  const add = (name, yes, why) => kinds.push({ name, yes, why });

  add(n % 2 ? "Odd" : "Even", true, n % 2 ? "Halving it leaves 1 over." : "It splits into two equal halves of " + fmt(n / 2) + ".");
  const sq = Math.round(Math.sqrt(n));
  add("Square number", sq * sq === n, fmt(sq) + " × " + fmt(sq) + " = " + fmt(n) + " — that many dots make a square.");
  const cb = Math.round(Math.cbrt(n));
  add("Cube number", cb * cb * cb === n, fmt(cb) + " × " + fmt(cb) + " × " + fmt(cb) + " = " + fmt(n) + ".");
  const tr = Math.round((Math.sqrt(8 * n + 1) - 1) / 2);
  add("Triangular number", tr * (tr + 1) / 2 === n, "1 + 2 + 3 + … + " + fmt(tr) + " = " + fmt(n) + " — that many dots make a triangle.");
  let p2 = 1, e2 = 0;
  while (p2 < n){ p2 *= 2; e2++; }
  add("Power of 2", p2 === n, "2 multiplied by itself " + e2 + " time" + (e2 === 1 ? "" : "s") + (e2 === 0 ? " (2⁰ = 1)." : "."));
  const fi = NX_FIB.indexOf(n);
  add("Fibonacci number", fi >= 0, "In 1, 1, 2, 3, 5, 8, 13 … each number is the two before it added together.");
  let f = 1, k = 1;
  while (f < n){ k++; f *= k; }
  add("Factorial", f === n && n > 1, "1 × 2 × … × " + k + " = " + fmt(n) + ", written " + k + "!");
  const rest = divSum - n;
  if (n > 1){
    add("Perfect number", rest === n, "Its divisors, apart from itself, add up to exactly " + fmt(n) + ". Very rare!");
    add("Abundant number", rest > n, "Its divisors, apart from itself, add up to " + fmt(rest) + " — more than the number.");
  }
  const cubes = [];
  for (let a = 1; 2 * a * a * a <= n; a++){
    const b = Math.round(Math.cbrt(n - a * a * a));
    if (a * a * a + b * b * b === n) cubes.push(a + "³ + " + b + "³");
  }
  add("Sum of two cubes", cubes.length > 0, cubes.join(" and ") + (cubes.length > 1 ? " — " + cubes.length + " different ways!" : "."));
  add("Palindrome", len > 1 && str === [...str].reverse().join(""), "It reads the same backwards.");
  add("Harshad number", len > 1 && n % dsum === 0, "It divides exactly by the sum of its digits, " + dsum + ".");
  const pw = digits.reduce((a, d) => a + d ** len, 0);
  add("Armstrong number", len > 1 && pw === n, digits.map(d => d + toSup(len)).join(" + ") + " = " + fmt(n) + " — each digit raised to the number of digits.");
  const chain = [n];
  let h = n;
  while (h !== 1 && h !== 4 && chain.length < 40){ h = [...String(h)].reduce((a, d) => a + d * d, 0); chain.push(h); }
  add("Happy number", h === 1, "Square its digits and add, again and again, and you reach 1: " + chain.slice(0, 8).map(fmt).join(" → ") + (chain.length > 8 ? " → … → 1" : "") + ".");
  if (fs.length === 1 && fs[0][1] === 1){
    const lo = nxIsPrime(n - 2), hi = nxIsPrime(n + 2);
    add("Twin prime", lo || hi, fmt(lo ? n - 2 : n) + " and " + fmt(lo ? n : n + 2) + " are both prime, only 2 apart.");
  }
  return kinds;
}
const SUP = "⁰¹²³⁴⁵⁶⁷⁸⁹";
const toSup = k => [...String(k)].map(d => SUP[d]).join("");

/* ---- the 3n + 1 game ---- */
function nxCollatz(n){
  // the path can climb past where plain numbers are exact, so it is kept exactly too
  let v = BigInt(n), peak = v, peakAt = 0;
  const exact = [v], seq = [n];
  while (v !== 1n){
    v = v & 1n ? 3n * v + 1n : v >> 1n;
    exact.push(v); seq.push(Number(v));
    if (v > peak){ peak = v; peakAt = seq.length - 1; }
  }
  return { seq, exact, peak, peakAt };
}

const nxCompact = v => v < 1e4 ? fmt(v) : v < 1e15
  ? new Intl.NumberFormat("en-US", { notation: "compact", maximumFractionDigits: 1 }).format(v) : v.toExponential(1).replace("e+", "e");
function nxTicks(max){
  const raw = max / 4, mag = 10 ** Math.floor(Math.log10(raw)), r = raw / mag;
  const step = (r <= 1 ? 1 : r <= 2 ? 2 : r <= 5 ? 5 : 10) * mag;
  const out = [0];
  // the top line always sits at or above the highest point, so nothing is clipped
  while (out[out.length - 1] < max) out.push(out.length * step);
  return out;
}
function drawCollatz(){
  const seq = NX.seq, box = $("nxChartBox"), cv = $("nxChart");
  if (!seq || !box.clientWidth) return;
  const W = box.clientWidth, H = box.clientHeight, dpr = DPR();
  cv.width = Math.round(W * dpr); cv.height = Math.round(H * dpr);
  cv.style.width = W + "px"; cv.style.height = H + "px";
  const ctx = cv.getContext("2d");
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  ctx.clearRect(0, 0, W, H);
  const max = Math.max(...seq), ticks = nxTicks(max), top = ticks[ticks.length - 1];
  ctx.font = "11px \"JetBrains Mono\", ui-monospace, monospace";
  const padL = Math.ceil(Math.max(...ticks.map(t => ctx.measureText(nxCompact(t)).width))) + 14, padR = 14, padT = 14, padB = 26;
  const pw = W - padL - padR, ph = H - padT - padB;
  const X = i => padL + (seq.length === 1 ? pw / 2 : i / (seq.length - 1) * pw), Y = v => padT + ph - v / top * ph;
  const muted = cssVar("--muted"), line = cssVar("--line"), accent = cssVar("--accent"), surface = cssVar("--surface-solid");
  // recessive grid and axis labels
  ctx.strokeStyle = line; ctx.lineWidth = 1; ctx.fillStyle = muted;
  ctx.textAlign = "right"; ctx.textBaseline = "middle";
  for (const t of ticks){
    const y = Math.round(Y(t)) + .5;
    ctx.beginPath(); ctx.moveTo(padL, y); ctx.lineTo(W - padR, y); ctx.stroke();
    ctx.fillText(nxCompact(t), padL - 8, y);
  }
  ctx.textAlign = "center"; ctx.textBaseline = "top";
  const steps = seq.length - 1, xs = steps <= 4 ? Array.from({ length: steps + 1 }, (_, i) => i) : [0, Math.round(steps / 4), Math.round(steps / 2), Math.round(steps * 3 / 4), steps];
  for (const i of xs) ctx.fillText(fmt(i), X(i), H - padB + 8);
  // the path itself
  ctx.strokeStyle = accent; ctx.lineWidth = 2; ctx.lineJoin = "round"; ctx.lineCap = "round";
  ctx.beginPath();
  seq.forEach((v, i) => i ? ctx.lineTo(X(i), Y(v)) : ctx.moveTo(X(i), Y(v)));
  ctx.stroke();
  const dot = (i, r) => {
    ctx.beginPath(); ctx.arc(X(i), Y(seq[i]), r + 2, 0, Math.PI * 2); ctx.fillStyle = surface; ctx.fill();
    ctx.beginPath(); ctx.arc(X(i), Y(seq[i]), r, 0, Math.PI * 2); ctx.fillStyle = accent; ctx.fill();
  };
  // label only the highest point
  const pk = NX.peakAt;
  dot(pk, 4);
  ctx.fillStyle = cssVar("--fg"); ctx.font = "600 11.5px \"JetBrains Mono\", ui-monospace, monospace";
  ctx.textBaseline = "bottom";
  ctx.textAlign = X(pk) < padL + 60 ? "left" : X(pk) > W - padR - 60 ? "right" : "center";
  ctx.fillText("highest: " + nxCompact(seq[pk]), X(pk), Y(seq[pk]) - 9);
  // hover: a crosshair and the point under it
  const hv = NX.hover;
  if (hv >= 0){
    ctx.strokeStyle = cssVar("--line-strong"); ctx.lineWidth = 1;
    ctx.beginPath(); ctx.moveTo(Math.round(X(hv)) + .5, padT); ctx.lineTo(Math.round(X(hv)) + .5, padT + ph); ctx.stroke();
    dot(hv, 4.5);
  }
  NX.geom = { padL, pw, X, Y };
}
function collatzHover(e){
  const g = NX.geom, seq = NX.seq, tip = $("nxTip");
  if (!g || !seq || seq.length < 2) return;
  const r = $("nxChartBox").getBoundingClientRect();
  const i = clamp(Math.round((e.clientX - r.left - g.padL) / g.pw * (seq.length - 1)), 0, seq.length - 1);
  if (i === NX.hover) return;
  NX.hover = i;
  drawCollatz();
  tip.innerHTML = "<b>" + fmtDigits(NX.exact[i].toString()) + "</b><span>step " + fmt(i)
    + (i ? (NX.exact[i - 1] & 1n ? " · odd, so ×3 + 1" : " · even, so halved") : " · the start") + "</span>";
  tip.hidden = false;
  const x = g.X(i), y = g.Y(seq[i]);
  const tw = tip.offsetWidth, th = tip.offsetHeight;
  tip.style.left = clamp(x - tw / 2, 4, r.width - tw - 4) + "px";
  tip.style.top = (y - th - 14 < 4 ? y + 14 : y - th - 14) + "px";
}

/* ---- the page ---- */
function exploreNumber(){
  let n;
  try { n = parseBig($("nxInput").value); }
  catch (e){ $("nxInput").classList.add("invalid"); toast("Type a whole number, like 360 or 2^20", true); return; }
  if (n < 1n || n > BigInt(NX_MAX)){
    $("nxInput").classList.add("invalid");
    toast("Pick a whole number from 1 to 1,000,000,000,000,000 — for bigger ones, try the Primes or Big Numbers tools", true);
    return;
  }
  $("nxInput").classList.remove("invalid");
  n = Number(n);
  NX.n = n;
  $("nxInput").value = fmt(n);

  const fs = nxFactor(n), divs = nxDivisors(fs), divSum = divs.reduce((a, b) => a + b, 0);
  const prime = n > 1 && fs.length === 1 && fs[0][1] === 1;
  let prev = n - 1; while (prev >= 2 && !nxIsPrime(prev)) prev--;
  let next = n + 1; while (!nxIsPrime(next)) next++;
  const factHtml = n === 1 ? "1" : fs.map(([p, e]) => fmt(p) + (e > 1 ? "<sup>" + e + "</sup>" : "")).join(" × ");
  const dsum = [...String(n)].reduce((a, d) => a + +d, 0);

  statTiles($("nxStats"), [
    ["Number", fmt(n) + "<small>" + String(n).length + " digit" + (n > 9 ? "s" : "") + "</small>", "big"],
    ["Prime?", (prime ? "Yes" : n === 1 ? "Neither" : "No")
      + "<small>" + (n === 1 ? "1 is a special case" : prev >= 2 ? "nearest primes " + fmt(prev) + " and " + fmt(next) : "next prime is " + fmt(next)) + "</small>", prime ? "ok" : ""],
    ["Prime factors", factHtml + "<small>" + (prime ? "it is its own only factor" : "multiply these to get it back") + "</small>"],
    ["Divisors", fmt(divs.length) + "<small>adding up to " + fmt(divSum) + "</small>"],
    ["Digit sum", fmt(dsum) + "<small>" + (n % 9 === 0 ? "divisible by 9" : n % 3 === 0 ? "divisible by 3" : "not divisible by 3") + "</small>"]
  ]);

  const kinds = nxKinds(n, fs, divSum), yes = kinds.filter(k => k.yes), no = kinds.filter(k => !k.yes);
  $("nxKinds").innerHTML = yes.map(k => '<div class="kind"><span class="tick" aria-hidden="true">✓</span><div><b>' + k.name + "</b><span>" + k.why + "</span></div></div>").join("")
    + (no.length ? '<p class="kinds-no"><span>Not:</span> ' + no.map(k => k.name.toLowerCase()).join(", ") + "</p>" : "");

  const roman = nxRoman(n), big = BigInt(n);
  $("nxWays").innerHTML = [
    ["In words", nxWords(n)],
    ["Roman numerals", roman || "too big — Roman numerals stop at 3,999"],
    ["Binary (base 2)", nxGroup(n.toString(2), 4)],
    ["Hexadecimal (base 16)", n.toString(16).toUpperCase()],
    ["Squared", fmtDigits((big * big).toString())],
    ["Square root", Number.isInteger(Math.sqrt(n)) ? fmt(Math.sqrt(n)) + " exactly" : "about " + Math.sqrt(n).toLocaleString("en-US", { maximumFractionDigits: 6 })],
    ["One over it", n === 1 ? "1" : "about " + (1 / n).toPrecision(6)]
  ].map(([k, v]) => "<div><dt>" + k + "</dt><dd>" + v + "</dd></div>").join("");

  const shown = divs.slice(0, 300);
  $("nxDivNote").textContent = fmt(divs.length) + " of them" + (divs.length > shown.length ? " · first " + shown.length + " shown" : "");
  $("nxDivs").innerHTML = shown.map(d => "<span>" + fmt(d) + "</span>").join("") + (divs.length > shown.length ? '<span class="x">…</span>' : "");

  const c = nxCollatz(n);
  NX.seq = c.seq; NX.exact = c.exact; NX.peakAt = c.peakAt; NX.hover = -1;
  $("nxTip").hidden = true;
  $("nxCollatzNote").textContent = n === 1 ? "already at 1" : "reaches 1 in " + fmt(c.seq.length - 1) + " steps · highest " + fmtDigits(c.peak.toString());
  drawCollatz();
}

function initNumbers(){
  $("nxGo").addEventListener("click", exploreNumber);
  $("nxInput").addEventListener("keydown", e => { if (e.key === "Enter") exploreNumber(); });
  $("nxPresets").addEventListener("click", e => {
    const b = e.target.closest("button[data-n]");
    if (!b) return;
    let v = b.dataset.n;
    if (v === "surprise"){
      v = Math.random() < 0.5 ? NX_SURPRISE[Math.floor(Math.random() * NX_SURPRISE.length)] : 1 + Math.floor(Math.random() * 100000);
      if (String(v) === $("nxInput").value.replace(/,/g, "")) v++;
    }
    $("nxInput").value = v;
    exploreNumber();
  });
  const box = $("nxChartBox");
  box.addEventListener("pointermove", collatzHover);
  box.addEventListener("pointerdown", collatzHover);
  box.addEventListener("pointerleave", () => { NX.hover = -1; $("nxTip").hidden = true; drawCollatz(); });
  if (window.ResizeObserver) new ResizeObserver(() => drawCollatz()).observe(box);
  themeListeners.push(drawCollatz);
}
