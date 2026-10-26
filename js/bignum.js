"use strict";
/* ================= big numbers: the worker =================
   Products are built as balanced trees so the big multiplications happen between
   numbers of similar size, which is where the engine's fast multiplication pays. */
function bigWorker(){
  let lastPost = 0;
  function post(phase, frac){
    const now = performance.now();
    if (now - lastPost < 70) return;
    lastPost = now;
    postMessage({ type: "progress", phase, frac });
  }
  /** a × (a+1) × … × b, as a product tree. */
  function prodRange(a, b){
    if (a > b) return 1n;
    if (b - a < 24){
      let p = 1n;
      for (let k = a; k <= b; k++) p *= BigInt(k);
      return p;
    }
    const m = Math.floor((a + b) / 2);
    return prodRange(a, m) * prodRange(m + 1, b);
  }
  function prodList(xs, lo, hi){
    if (hi - lo <= 16){ let p = 1n; for (let k = lo; k < hi; k++) p *= BigInt(xs[k]); return p; }
    const m = (lo + hi) >> 1;
    return prodList(xs, lo, m) * prodList(xs, m, hi);
  }
  /** F(n) by fast doubling: F(2k) = F(k)(2F(k+1) − F(k)), F(2k+1) = F(k)² + F(k+1)². */
  function fib(n){
    let a = 0n, b = 1n;
    const bits = n.toString(2);
    for (let i = 0; i < bits.length; i++){
      const c = a * (2n * b - a), d = a * a + b * b;
      if (bits[i] === "1"){ a = d; b = c + d; } else { a = c; b = d; }
      post("doubling, bit " + (i + 1) + " of " + bits.length, (i + 1) / bits.length * 0.6);
    }
    return a;
  }
  function primesUpTo(n){
    const sieve = new Uint8Array(n + 1), out = [];
    for (let i = 2; i <= n; i++){
      if (sieve[i]) continue;
      out.push(i);
      if (i * i <= n) for (let j = i * i; j <= n; j += i) sieve[j] = 1;
    }
    return out;
  }
  onmessage = e => {
    const { op, a, b } = e.data;
    try {
      const t0 = performance.now();
      let v;
      post("multiplying", 0.1);
      if (op === "fact") v = prodRange(2, Number(a));
      else if (op === "fib") v = fib(Number(a));
      else if (op === "pow") v = BigInt(a) ** BigInt(b);
      else if (op === "binom"){
        const n = Number(a), k0 = Number(b), k = Math.min(k0, n - k0);
        v = k < 0 ? 0n : prodRange(n - k + 1, n) / prodRange(1, k);
      }
      else if (op === "catalan"){ const n = Number(a); v = prodRange(n + 2, 2 * n) / prodRange(1, n); }
      else if (op === "primorial"){ const ps = primesUpTo(Number(a)); v = prodList(ps, 0, ps.length); }
      const tCompute = performance.now() - t0;
      postMessage({ type: "progress", phase: "writing out the decimal digits", frac: 0.75 });
      const s = v.toString();
      postMessage({ type: "done", s, ms: performance.now() - t0, tCompute });
    } catch (err){
      postMessage({ type: "error", message: String(err && err.message || err) });
    }
  };
}

/* ================= big numbers: the page ================= */
const BIG_OPS = {
  fact:      { a: "n", def: ["1000"], name: (a) => a + "!", what: "every whole number up to n, multiplied together" },
  fib:       { a: "n", def: ["10000"], name: (a) => "F(" + a + ")", what: "the n-th Fibonacci number" },
  pow:       { a: "a (base)", b: "b (exponent)", def: ["2", "1000"], name: (a, b) => a + "^" + b, what: "a multiplied by itself b times" },
  binom:     { a: "n", b: "k", def: ["1000", "500"], name: (a, b) => "C(" + a + ", " + b + ")", what: "ways to choose k of n" },
  catalan:   { a: "n", def: ["1000"], name: (a) => "Catalan(" + a + ")", what: "ways to match up n pairs of brackets" },
  primorial: { a: "n", def: ["10000"], name: (a) => a + "#", what: "the product of every prime ≤ n" }
};
const BG = { op: "fact", s: "", label: "", job: new Job(bigWorker), stream: null, progress: null };

function setBigOp(op){
  BG.op = op;
  const spec = BIG_OPS[op];
  $("bigALabel").textContent = spec.a;
  $("bigBField").hidden = !spec.b;
  if (spec.b) $("bigBLabel").textContent = spec.b;
  $("bigA").value = spec.def[0];
  if (spec.b) $("bigB").value = spec.def[1];
}

async function runBig(){
  const spec = BIG_OPS[BG.op];
  let a, b;
  try {
    if (BG.op === "pow"){
      a = parseBig($("bigA").value);
      b = parseBig($("bigB").value);
      if (b < 0n) throw new Error("the exponent must be 0 or more");
    } else {
      a = BigInt(parseCount($("bigA").value));
      if (spec.b){
        b = BigInt(parseCount($("bigB").value));
        if (b > a) throw new Error("k cannot be bigger than n");
      }
    }
  } catch (e){
    toast(/Cannot convert NaN/.test(e.message) ? "Type a whole number, like 1000 or 1e6" : e.message, true);
    return;
  }
  const label = spec.name(String(a), b === undefined ? "" : String(b));
  $("bigRun").disabled = true; $("bigCancel").hidden = false;
  BG.progress.start("computing " + label);
  try {
    const res = await BG.job.run({ op: BG.op, a: String(a), b: b === undefined ? null : String(b) },
      p => BG.progress.set(p.phase, p.frac));
    BG.s = res.s; BG.label = label;
    renderBig(res);
    toast(label + " has " + fmt(res.s.replace("-", "").length) + " digits — computed in " + fmtMs(res.ms));
  } catch (err){
    if (!err.cancelled) toast("Could not finish: " + explainError(err), true);
    else toast("Cancelled");
  } finally {
    BG.progress.stop();
    $("bigRun").disabled = false; $("bigCancel").hidden = true;
  }
}

function renderBig(res){
  const s = BG.s, neg = s[0] === "-", digits = neg ? s.slice(1) : s, n = digits.length;
  const counts = digitCounts(digits);
  let sum = 0;
  counts.forEach((c, d) => sum += c * d);
  let tz = 0;
  for (let i = n - 1; i >= 0 && digits[i] === "0"; i--) tz++;
  const sci = n > 1 ? (neg ? "−" : "") + digits[0] + "." + digits.slice(1, 10) + " × 10<sup>" + fmt(n - 1) + "</sup>" : s;
  statTiles($("bigStats"), [
    ["Value", BG.label + "<small>" + BIG_OPS[BG.op].what + "</small>"],
    ["Digits", fmt(n), "big"],
    ["Approximately", sci],
    ["Digit sum", fmt(sum) + "<small>" + (sum % 9 === 0 ? "divisible by 9" : sum % 3 === 0 ? "divisible by 3" : "not divisible by 3") + "</small>"],
    ["Trailing zeros", fmt(tz)],
    ["Computed in", fmtMs(res.ms) + "<small>" + fmtMs(res.tCompute) + " arithmetic, the rest writing decimals</small>"]
  ]);
  renderLegend($("bigLegend"), counts, d => PALETTE[d]);
  $("bigTitle").textContent = BG.label;
  $("bigLead").textContent = (neg ? "−" : "") + (n > 80 ? digits.slice(0, 80) + "…" : digits);
  BG.stream.set(digits);
}

function initBig(){
  BG.progress = new Progress($("bigProgress"), $("bigProgressText"));
  BG.stream = new DigitStream($("bigStream"), $("bigStreamInner"), $("bigStreamNote"));
  segWire($("bigOp"), "op", op => setBigOp(op));
  $("bigRun").addEventListener("click", runBig);
  $("bigCancel").addEventListener("click", () => BG.job.cancel());
  ["bigA", "bigB"].forEach(id => $(id).addEventListener("keydown", e => { if (e.key === "Enter") runBig(); }));
  $("bigCopy").addEventListener("click", () => { if (BG.s) copyText(BG.s, fmt(BG.s.length) + " digits"); });
  $("bigSaveTxt").addEventListener("click", () => {
    if (!BG.s) return;
    saveText(BG.s + "\n", BG.label.replace(/[^\w#!^(),-]+/g, "_") + ".txt", "text/plain");
  });
}
