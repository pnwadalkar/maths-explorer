"use strict";
/* ================= primes: the worker =================
   One worker, several jobs: sieve a spiral's worth of numbers, test or factorise a
   whole number of any size, step to the next prime, or count the primes below x. */
function primesWorker(){
  let lastPost = 0;
  function post(phase, frac, extra){
    const now = performance.now();
    if (now - lastPost < 70 && !extra) return;
    lastPost = now;
    postMessage(Object.assign({ type: "progress", phase, frac }, extra || {}));
  }
  function smallPrimes(limit){
    const sieve = new Uint8Array(limit + 1), out = [];
    for (let i = 2; i <= limit; i++){
      if (sieve[i]) continue;
      out.push(i);
      for (let j = i * i; j <= limit; j += i) sieve[j] = 1;
    }
    return out;
  }

  /* ---- the spiral: sieve [start, start + side² − 1] in segments ---- */
  function ulam({ side, start }){
    const N = side * side, hi = start + N - 1;
    const base = smallPrimes(Math.floor(Math.sqrt(hi)) + 1);
    const bits = new Uint8Array(Math.ceil(N / 8));
    const R = Math.min(side, 1024), dens = new Uint32Array(R * R);
    const c = (side - 1) / 2;
    const SEG = 1 << 20, seg = new Uint8Array(SEG);
    let count = 0, twins = 0, prev = -1, gap = 0, gapAt = 0, lastPrime = -1;
    // walk the spiral alongside the sieve: right 1, up 1, left 2, down 2, right 3 …
    let x = 0, y = 0, dir = 0, leg = 1, legLeft = 1, legsDone = 0;
    const DX = [1, 0, -1, 0], DY = [0, 1, 0, -1];
    for (let lo = 0; lo < N; lo += SEG){
      const len = Math.min(SEG, N - lo);
      seg.fill(0, 0, len);
      const vlo = start + lo, vhi = vlo + len - 1;
      for (const p of base){
        if (p * p > vhi) break;
        let m = Math.max(p * p, Math.ceil(vlo / p) * p);
        for (; m <= vhi; m += p) seg[m - vlo] = 1;
      }
      for (let k = 0; k < len; k++){
        const t = lo + k, v = vlo + k;
        if (!seg[k] && v >= 2){
          bits[t >> 3] |= 1 << (t & 7);
          count++;
          if (lastPrime >= 0){
            if (v - lastPrime === 2) twins++;
            if (v - lastPrime > gap){ gap = v - lastPrime; gapAt = lastPrime; }
          }
          lastPrime = v;
          const gx = x + c, gy = c - y;
          dens[Math.floor(gy * R / side) * R + Math.floor(gx * R / side)]++;
        }
        // step to the next spiral position
        x += DX[dir]; y += DY[dir];
        if (--legLeft === 0){
          dir = (dir + 1) & 3; legsDone++;
          if ((legsDone & 1) === 0) leg++;
          legLeft = leg;
        }
      }
      post("sieving", (lo + len) / N);
    }
    return { bits: bits.buffer, dens: dens.buffer, R, count, twins, gap, gapAt, transfer: true };
  }

  /* ---- arbitrary-size primality ---- */
  const SMALL = smallPrimes(65536).map(BigInt);
  function modpow(b, e, m){
    let r = 1n;
    b %= m;
    while (e > 0n){
      if (e & 1n) r = r * b % m;
      e >>= 1n;
      b = b * b % m;
    }
    return r;
  }
  function randomBelow(n){
    const digits = n.toString(16).length;
    let s = "";
    for (let i = 0; i < digits; i++) s += Math.floor(Math.random() * 16).toString(16);
    return BigInt("0x" + s) % n;
  }
  const DET_LIMIT = 3317044064679887385961981n;   // the first 13 prime bases settle every n below this
  /** { prime, proof: "deterministic" | "probable", factor? } */
  function testPrime(n){
    if (n < 2n) return { prime: false };
    for (const p of SMALL.slice(0, 200)){
      if (n === p) return { prime: true, proof: "deterministic" };
      if (n % p === 0n) return { prime: false, factor: p };
    }
    let d = n - 1n, s = 0;
    while ((d & 1n) === 0n){ d >>= 1n; s++; }
    const det = n < DET_LIMIT;
    const bases = SMALL.slice(0, 13);
    if (!det) for (let k = 0; k < 24; k++) bases.push(2n + randomBelow(n - 4n));
    for (const a of bases){
      let x = modpow(a, d, n);
      if (x === 1n || x === n - 1n) continue;
      let comp = true;
      for (let r = 1; r < s; r++){
        x = x * x % n;
        if (x === n - 1n){ comp = false; break; }
      }
      if (comp) return { prime: false };
    }
    return { prime: true, proof: det ? "deterministic" : "probable", rounds: bases.length };
  }
  const isPrime = n => testPrime(n).prime;

  function gcd(a, b){ while (b){ const t = a % b; a = b; b = t; } return a; }
  /** Pollard's rho with Brent's cycle finding and batched gcds. */
  function rho(n){
    if ((n & 1n) === 0n) return 2n;
    for (let c = 1n; ; c++){
      let y = randomBelow(n), r = 1, q = 1n, g = 1n, x = 0n, ys = 0n;
      const m = 128;
      do {
        x = y;
        for (let i = 0; i < r; i++) y = (y * y + c) % n;
        let k = 0;
        do {
          ys = y;
          const lim = Math.min(m, r - k);
          for (let i = 0; i < lim; i++){
            y = (y * y + c) % n;
            q = q * (x > y ? x - y : y - x) % n;
          }
          g = gcd(q, n);
          k += m;
        } while (k < r && g === 1n);
        r *= 2;
        post("searching for a factor (Pollard rho, " + r.toLocaleString("en-US") + " steps)", null);
      } while (g === 1n);
      if (g === n){
        do { ys = (ys * ys + c) % n; g = gcd(x > ys ? x - ys : ys - x, n); } while (g === 1n);
      }
      if (g !== n) return g;
    }
  }
  function factorise(n){
    const found = [];
    const report = () => post("factorising", null, { found: found.map(String) });
    if (n < 0n){ found.push(-1n); n = -n; }
    for (const p of SMALL){
      if (p * p > n) break;
      while (n % p === 0n){ found.push(p); n /= p; }
    }
    report();
    const stack = n > 1n ? [n] : [];
    while (stack.length){
      const m = stack.pop();
      if (m === 1n) continue;
      if (isPrime(m)){ found.push(m); report(); continue; }
      // a perfect square defeats rho's cycle quickly enough, but check the cheap case first
      const d = rho(m);
      stack.push(d, m / d);
    }
    found.sort((a, b) => a < b ? -1 : a > b ? 1 : 0);
    return found;
  }
  function stepPrime(n, dir){
    let k = n + BigInt(dir), tried = 0;
    if (dir < 0 && k < 2n) return null;
    if (k <= 2n) return 2n;
    if ((k & 1n) === 0n) k += BigInt(dir);
    for (;;){
      if (k < 2n) return dir < 0 ? 2n : null;
      if (isPrime(k)) return k;
      k += BigInt(2 * dir);
      if (++tried % 50 === 0) post("testing candidates (" + tried.toLocaleString("en-US") + " so far)", null);
    }
  }

  /* ---- π(x): Lucy Hedgehog's method, O(x^¾) time and O(√x) memory ---- */
  function countPrimes(x){
    if (x < 2) return 0;
    const r = Math.floor(Math.sqrt(x));
    const small = new Float64Array(r + 1), large = new Float64Array(r + 1);
    for (let i = 1; i <= r; i++){ small[i] = i - 1; large[i] = Math.floor(x / i) - 1; }
    for (let p = 2; p <= r; p++){
      if (small[p] === small[p - 1]) continue;
      const sp = small[p - 1], p2 = p * p;
      const lim = Math.min(r, Math.floor(x / p2));
      for (let i = 1; i <= lim; i++){
        const d = i * p;
        large[i] -= (d <= r ? large[d] : small[Math.floor(x / d)]) - sp;
      }
      for (let i = r; i >= p2; i--) small[i] -= small[Math.floor(i / p)] - sp;
      post("sieving with p = " + p.toLocaleString("en-US"), Math.sqrt(p / r));
    }
    return large[1];
  }

  onmessage = e => {
    const m = e.data;
    try {
      const t0 = performance.now();
      let res;
      if (m.op === "ulam") res = ulam(m);
      else {
        const n = BigInt(m.n);
        if (m.op === "test") res = testPrime(n);
        else if (m.op === "factor") res = { factors: factorise(n).map(String) };
        else if (m.op === "next") res = { p: String(stepPrime(n, 1)) };
        else if (m.op === "prev"){ const p = stepPrime(n, -1); res = { p: p === null ? null : String(p) }; }
        else if (m.op === "count") res = { count: countPrimes(Number(n)) };
        if (res.factor) res.factor = String(res.factor);
      }
      res.type = "done";
      res.ms = performance.now() - t0;
      if (res.transfer) postMessage(res, [res.bits, res.dens]);
      else postMessage(res);
    } catch (err){
      postMessage({ type: "error", message: String(err && err.message || err) });
    }
  };
}

/* ================= the spiral on the page ================= */
const U = {
  side: 0, start: 1, N: 0, bits: null, dens: null, R: 0, densImg: null,
  colour: "plain", stats: null,
  job: new Job(primesWorker), tools: new Job(primesWorker),
  pz: null, progress: null, ptProgress: null
};
const uIsPrimeT = t => t >= 0 && t < U.N && (U.bits[t >> 3] >> (t & 7) & 1) === 1;
/** Spiral index t (0 at the centre) of grid cell (gx, gy). */
function ulamIndex(gx, gy){
  const c = (U.side - 1) / 2, x = gx - c, y = c - gy;
  const n = Math.max(Math.abs(x), Math.abs(y));
  if (n === 0) return 0;
  const b = (2 * n - 1) * (2 * n - 1);
  if (x === n && y > -n) return b + (y + n - 1);
  if (y === n) return b + 2 * n - 1 + (n - x);
  if (x === -n) return b + 4 * n - 1 + (n - y);
  return b + 6 * n - 1 + (x + n);
}
function ulamColours(dark){
  return {
    bg: dark ? "#080B14" : "#FBFBFE",
    prime: (gx, gy) => {
      const c = (U.side - 1) / 2, r = Math.max(Math.abs(gx - c), Math.abs(gy - c)) / Math.max(1, c);
      return rgbCss(hslToRgb(250 - r * 70, .9, dark ? .7 : .48));
    },
    twin: dark ? "#FF7EB0" : "#D6336C",
    dim: dark ? "rgba(139,139,255,.32)" : "rgba(79,79,224,.3)",
    last: { 1: dark ? "#8B8BFF" : "#4F4FE0", 3: dark ? "#3DD6E0" : "#0E8FA0", 7: dark ? "#FF7EB0" : "#D6336C",
            9: dark ? "#F5C84B" : "#B7791F", 2: dark ? "#3DDC97" : "#0F9F6E", 5: dark ? "#3DDC97" : "#0F9F6E" },
    text: dark ? "#E9ECF5" : "#10131C",
    textDim: dark ? "rgba(233,236,245,.35)" : "rgba(16,19,28,.35)"
  };
}
function buildDensityImage(){
  const R = U.R, dark = isDark(), dens = U.dens;
  const cv = document.createElement("canvas");
  cv.width = R; cv.height = R;
  const ctx = cv.getContext("2d"), img = ctx.createImageData(R, R), px = img.data;
  const per = (U.side / R) ** 2;
  // primes thin out like 1/ln n, so normalise against the densest bucket, not against 1
  let peak = 0;
  for (let k = 0; k < dens.length; k++) if (dens[k] > peak) peak = dens[k];
  const norm = per === 1 ? 1 : peak || 1;
  const bg = dark ? [8, 11, 20] : [251, 251, 254];
  const c = (R - 1) / 2;
  for (let gy = 0; gy < R; gy++) for (let gx = 0; gx < R; gx++){
    const k = gy * R + gx, a = Math.min(1, dens[k] / norm) ** (per === 1 ? 1 : 0.8);
    const r = Math.max(Math.abs(gx - c), Math.abs(gy - c)) / Math.max(1, c);
    const fg = hslToRgb(250 - r * 70, .9, dark ? .7 : .48), o = k * 4;
    px[o] = bg[0] + (fg[0] - bg[0]) * a; px[o+1] = bg[1] + (fg[1] - bg[1]) * a; px[o+2] = bg[2] + (fg[2] - bg[2]) * a; px[o+3] = 255;
  }
  ctx.putImageData(img, 0, 0);
  U.densImg = cv; U.densDark = dark;
}
function ulamSource(){
  const side = U.side;
  return {
    kind: "ulam", w: side, h: side, pad: 10, maxScale: 120,
    title: "Ulam spiral of " + fmt(U.N) + " numbers from " + fmt(U.start),
    meta: fmt(U.stats.count) + " primes",
    filename: "ulam-" + side + "-from-" + U.start + ".png",
    paint(ctx, s, vis){
      const dark = isDark(), col = ulamColours(dark);
      if (s < 1.5){
        if (!U.densImg || U.densDark !== dark) buildDensityImage();
        ctx.imageSmoothingEnabled = side * s < U.R;
        ctx.drawImage(U.densImg, 0, 0, side * s, side * s);
        return;
      }
      const x0 = vis ? Math.max(0, vis.x0) : 0, y0 = vis ? Math.max(0, vis.y0) : 0;
      const x1 = vis ? Math.min(side * s, vis.x1) : side * s, y1 = vis ? Math.min(side * s, vis.y1) : side * s;
      ctx.fillStyle = col.bg;
      ctx.fillRect(x0, y0, x1 - x0, y1 - y0);
      const c0 = Math.floor(x0 / s), c1 = Math.min(side - 1, Math.ceil(x1 / s));
      const r0 = Math.floor(y0 / s), r1 = Math.min(side - 1, Math.ceil(y1 / s));
      const text = s >= 26, gap = s >= 6 ? Math.max(1, s * 0.08) : 0;
      if (text){
        const w = String(U.start + U.N - 1).length;
        ctx.font = "500 " + Math.min(s * 0.36, s * 0.86 / (w * 0.6)).toFixed(1) + "px \"JetBrains Mono\", ui-monospace, monospace";
        ctx.textAlign = "center"; ctx.textBaseline = "middle";
      }
      for (let gy = r0; gy <= r1; gy++) for (let gx = c0; gx <= c1; gx++){
        const t = ulamIndex(gx, gy), prime = uIsPrimeT(t), v = U.start + t;
        if (prime){
          let fill;
          if (U.colour === "twin") fill = uIsPrimeT(t - 2) || uIsPrimeT(t + 2) || v === 3 ? col.twin : col.dim;
          else if (U.colour === "last") fill = col.last[v % 10];
          else fill = col.prime(gx, gy);
          ctx.fillStyle = fill;
          if (s >= 6){
            const rr = Math.min(6, s * 0.18);
            ctx.beginPath();
            if (ctx.roundRect) ctx.roundRect(gx * s + gap, gy * s + gap, s - gap * 2, s - gap * 2, rr);
            else ctx.rect(gx * s + gap, gy * s + gap, s - gap * 2, s - gap * 2);
            ctx.fill();
          } else ctx.fillRect(gx * s, gy * s, s, s);
        }
        if (text){
          ctx.fillStyle = prime ? (dark ? "#0A0B1A" : "#FFFFFF") : col.textDim;
          ctx.fillText(String(v), gx * s + s / 2, gy * s + s / 2 + s * 0.02);
        }
      }
      // ring the centre
      const cc = (side - 1) / 2;
      ctx.strokeStyle = "#F5C84B"; ctx.lineWidth = Math.max(1.5, Math.min(3, s / 10));
      ctx.strokeRect(cc * s + .5, cc * s + .5, s - 1, s - 1);
    },
    probe(x, y){
      const gx = Math.floor(x), gy = Math.floor(y);
      if (gx < 0 || gy < 0 || gx >= side || gy >= side) return "";
      const t = ulamIndex(gx, gy), v = U.start + t;
      const p = uIsPrimeT(t);
      let s = fmt(v) + (p ? " is prime" : " is not prime");
      if (p && (uIsPrimeT(t - 2) || uIsPrimeT(t + 2))) s += " — a twin prime";
      return s + "  ·  " + fmt(t) + " steps from the centre";
    },
    detail(pz){ const v = pz.visibleContent(); pz.centerOn((v.x0 + v.x1) / 2, (v.y0 + v.y1) / 2, 34); },
    zoomNote: s => (s < 1 ? s.toFixed(3) : s.toFixed(1)) + " px per number",
    png(){
      const s = side <= 2048 ? Math.max(1, Math.floor(2048 / side)) : 2048 / side;
      const out = document.createElement("canvas");
      out.width = Math.max(1, Math.round(side * s)); out.height = out.width;
      this.paint(out.getContext("2d"), s, null);
      return out;
    }
  };
}

async function buildUlam(){
  let side = parseCount($("ulamSide").value);
  let start;
  try { start = Number(parseBig($("ulamStart").value || "1")); } catch (e) { start = NaN; }
  if (!Number.isFinite(side) || side < 1){ $("ulamSide").classList.add("invalid"); toast("Type a side length, like 401 or 2001", true); return; }
  if (!Number.isFinite(start) || start < 1){ $("ulamStart").classList.add("invalid"); toast("The centre number must be a positive whole number", true); return; }
  $("ulamSide").classList.remove("invalid"); $("ulamStart").classList.remove("invalid");
  if (side % 2 === 0){ side++; toast("Side rounded up to " + fmt(side) + " so the centre number sits in the middle cell"); }
  if (start + side * side > Number.MAX_SAFE_INTEGER){ toast("That spiral would pass 2^53 — lower the centre number or the side", true); return; }
  $("ulamSide").value = fmt(side);
  $("ulamBuild").disabled = true; $("ulamCancel").hidden = false;
  U.progress.start("sieving " + fmt(side * side) + " numbers");
  try {
    const res = await U.job.run({ op: "ulam", side, start }, p => U.progress.set(p.phase + " " + fmt(side * side) + " numbers", p.frac));
    U.side = side; U.start = start; U.N = side * side;
    U.bits = new Uint8Array(res.bits); U.dens = new Uint32Array(res.dens); U.R = res.R; U.densImg = null;
    U.stats = res;
    const hi = start + U.N - 1;
    const expect = start === 1 ? Math.round(hi / Math.log(hi)) : null;
    statTiles($("ulamStats"), [
      ["Numbers", fmt(start) + " … " + fmt(hi) + "<small>" + fmt(side) + " × " + fmt(side) + " spiral</small>"],
      ["Primes", fmt(res.count), "big"],
      ["Density", (100 * res.count / U.N).toFixed(2) + "%<small>" + (expect ? "N / ln N predicts " + fmt(expect) : "1 / ln N ≈ " + (100 / Math.log(hi)).toFixed(2) + "% at the edge") + "</small>"],
      ["Twin prime pairs", fmt(res.twins)],
      ["Largest gap", fmt(res.gap) + (res.gap ? "<small>after " + fmt(res.gapAt) + "</small>" : "")],
      ["Sieved in", fmtMs(res.ms)]
    ]);
    $("ulamTitle").textContent = "Ulam spiral";
    $("ulamNote").textContent = fmt(side) + " × " + fmt(side) + " from " + fmt(start);
    U.pz.setSource(ulamSource());
  } catch (err){
    if (!err.cancelled) toast("Could not draw the spiral: " + explainError(err), true);
  } finally {
    U.progress.stop();
    $("ulamBuild").disabled = false; $("ulamCancel").hidden = true;
  }
}

/* ================= prime tools ================= */
function bigShort(s, keep){
  keep = keep || 60;
  return s.length <= keep * 2 + 10 ? s : s.slice(0, keep) + "…" + s.slice(-keep) + " (" + fmt(s.length) + " digits)";
}
function factorHtml(list){
  const counts = new Map();
  list.forEach(f => counts.set(f, (counts.get(f) || 0) + 1));
  return [...counts].map(([f, k]) => "<span>" + bigShort(f, 30) + (k > 1 ? "<sup>" + k + "</sup>" : "") + "</span>")
    .join('<span class="x">×</span>');
}
async function primeTool(op){
  const out = $("ptOut");
  let n;
  try { n = parseBig($("ptInput").value); }
  catch (e){ $("ptInput").classList.add("invalid"); out.innerHTML = '<p class="hint">' + e.message + "</p>"; return; }
  $("ptInput").classList.remove("invalid");
  const s = n.toString();
  if (op === "count"){
    if (n < 0n || n > 10n ** 15n){
      out.innerHTML = '<p class="hint">Counting needs about 16·√x bytes of memory, so it runs up to 10<sup>15</sup> — '
        + "past that it would need more memory than a browser tab gets.</p>";
      return;
    }
  }
  if (op === "factor" && n === 0n){ out.innerHTML = '<p class="hint">0 is divisible by everything — it has no prime factorisation.</p>'; return; }
  const labels = { test: "testing", factor: "factorising", next: "looking for the next prime", prev: "looking for the previous prime", count: "counting primes" };
  $("ptCancel").hidden = false;
  document.querySelectorAll("#panel-primes [data-op]").forEach(b => b.disabled = true);
  U.ptProgress.start(labels[op] + " " + bigShort(s, 14));
  let found = [];
  try {
    const res = await U.tools.run({ op, n: s }, p => {
      if (p.found){ found = p.found; out.innerHTML = '<div class="pt-result"><div class="pt-num">found so far</div><div class="factors">' + factorHtml(found) + "</div></div>"; }
      U.ptProgress.set(p.phase, p.frac);
    });
    const head = '<div class="pt-num">n = ' + bigShort(s) + " · " + fmt(s.replace("-", "").length) + " digits · " + fmtMs(res.ms) + "</div>";
    let html = "";
    if (op === "test"){
      html = res.prime
        ? '<div class="pt-verdict yes">Prime</div>' + head + '<div class="pt-num">'
          + (res.proof === "deterministic" ? "Proven: Miller–Rabin with the first 13 prime bases is exact below 3.3 × 10²⁴."
             : "Probable prime: passed " + res.rounds + " Miller–Rabin rounds — the chance a composite survives is below 4^−" + res.rounds + ".") + "</div>"
        : '<div class="pt-verdict no">Not prime</div>' + head + (res.factor ? '<div class="pt-num">divisible by ' + res.factor + "</div>" : '<div class="pt-num">a Miller–Rabin witness proves it composite — try Factorise</div>');
    } else if (op === "factor"){
      const f = res.factors;
      html = '<div class="pt-verdict ' + (f.length === 1 ? "yes" : "") + '">' + (f.length === 1 ? "Prime — it is its own only factor" : f.length + " prime factors") + "</div>"
        + head + '<div class="factors">' + factorHtml(f) + "</div>";
    } else if (op === "next" || op === "prev"){
      if (res.p === null) html = '<div class="pt-verdict">No prime below ' + s + "</div>";
      else {
        const gap = BigInt(res.p) - n;
        html = '<div class="pt-verdict yes">' + bigShort(res.p, 40) + "</div>" + head
          + '<div class="pt-num">' + (op === "next" ? "the next prime, " + gap + " above" : "the previous prime, " + (-gap) + " below") + "</div>";
        $("ptInput").dataset.last = res.p;
      }
    } else if (op === "count"){
      const x = Number(n), ln = Math.log(x);
      let li = 0.5772156649015329 + Math.log(ln), term = 1;
      for (let k = 1; k < 400; k++){ term *= ln / k; li += term / k; if (term / k < 1e-17 * li) break; }
      html = '<div class="pt-verdict">π(' + fmt(x) + ") = " + fmt(res.count) + "</div>" + head
        + '<div class="pt-num">x / ln x ≈ ' + fmt(Math.round(x / ln)) + " · li(x) ≈ " + fmt(Math.round(li))
        + " — Gauss’s li(x) is off by only " + fmt(Math.round(li - res.count)) + "</div>";
    }
    out.innerHTML = '<div class="pt-result">' + html + "</div>";
  } catch (err){
    if (err.cancelled){
      out.innerHTML = found.length ? '<div class="pt-result"><div class="pt-num">cancelled — factors found so far</div><div class="factors">' + factorHtml(found) + "</div></div>"
        : '<p class="hint">Cancelled.</p>';
    } else out.innerHTML = '<p class="hint">Could not finish: ' + explainError(err) + "</p>";
  } finally {
    U.ptProgress.stop();
    $("ptCancel").hidden = true;
    document.querySelectorAll("#panel-primes [data-op]").forEach(b => b.disabled = false);
  }
}

function initPrimes(){
  U.progress = new Progress($("ulamProgress"), $("ulamProgressText"));
  U.ptProgress = new Progress($("ptProgress"), $("ptProgressText"));
  U.pz = new PanZoom($("ulamStage"), {
    onProbe: txt => { $("ulamHover").textContent = txt || "Zoom in far enough and every number is written in its cell."; }
  });
  $("ulamBuild").addEventListener("click", buildUlam);
  $("ulamCancel").addEventListener("click", () => U.job.cancel());
  ["ulamSide", "ulamStart"].forEach(id => $(id).addEventListener("keydown", e => { if (e.key === "Enter") buildUlam(); }));
  $("ulamPresets").addEventListener("click", e => {
    const b = e.target.closest("button[data-side]");
    if (!b) return;
    $("ulamSide").value = fmt(+b.dataset.side);
    $("ulamStart").value = b.dataset.start;
    buildUlam();
  });
  segWire($("ulamColour"), "m", m => { U.colour = m; U.pz.paint(); viewer.repaint(); });
  $("ulamFull").addEventListener("click", () => { if (U.bits) viewer.show(ulamSource()); });
  $("ulamSave").addEventListener("click", () => { if (U.bits){ const s = ulamSource(); savePng(s.png(), s.filename); } });
  document.querySelectorAll("#panel-primes [data-op]").forEach(b => b.addEventListener("click", () => primeTool(b.dataset.op)));
  $("ptInput").addEventListener("keydown", e => { if (e.key === "Enter") primeTool("test"); });
  $("ptCancel").addEventListener("click", () => U.tools.cancel());
  themeListeners.push(() => { U.densImg = null; if (U.bits) U.pz.paint(); });
}
