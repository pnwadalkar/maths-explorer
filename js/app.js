"use strict";
/* ================= wiring ================= */
const TOOLS = ["pi", "num", "msq", "primes", "pascal", "big", "fractal"];
const started = new Set();
/* Each tool does its first piece of work the first time it is shown, so opening the
   page costs only the tool you land on. */
const FIRST_RUN = {
  pi: () => computeConstant(),
  num: () => exploreNumber(),
  pascal: () => buildPascal(),
  msq: () => buildSquare(),
  primes: () => buildUlam(),
  big: () => runBig(),
  fractal: () => FR.pz.setSource(fractalSource())
};

function showTool(which, fromHash){
  if (!TOOLS.includes(which)) which = "pi";
  TOOLS.forEach(t => {
    $("tab-" + t).setAttribute("aria-selected", String(t === which));
    $("tab-" + t).tabIndex = t === which ? 0 : -1;
    $("panel-" + t).hidden = t !== which;
  });
  if (!started.has(which)){ started.add(which); FIRST_RUN[which](); }
  try { localStorage.setItem("maths-engine-tool", which); } catch (e) {}
  if (!fromHash && location.hash !== "#" + which) history.replaceState(null, "", "#" + which);
  const tab = $("tab-" + which);
  if (tab.scrollIntoView && window.innerWidth < 1000) tab.scrollIntoView({ block: "nearest", inline: "center", behavior: "smooth" });
}

document.querySelector(".tools").addEventListener("click", e => {
  const b = e.target.closest("button[data-tool]");
  if (b) showTool(b.dataset.tool);
});
document.querySelector(".tools").addEventListener("keydown", e => {
  if (e.key !== "ArrowRight" && e.key !== "ArrowLeft") return;
  const cur = TOOLS.findIndex(t => $("tab-" + t).getAttribute("aria-selected") === "true");
  const next = TOOLS[(cur + (e.key === "ArrowRight" ? 1 : TOOLS.length - 1)) % TOOLS.length];
  showTool(next);
  $("tab-" + next).focus();
  e.preventDefault();
});
window.addEventListener("hashchange", () => showTool(location.hash.slice(1), true));
document.querySelector(".brand").addEventListener("click", e => { e.preventDefault(); showTool("pi"); window.scrollTo({ top: 0, behavior: "smooth" }); });

$("themeDark").addEventListener("click", () => applyTheme("dark", true));
$("themeLight").addEventListener("click", () => applyTheme("light", true));
$("themeAuto").addEventListener("click", () => applyTheme("auto", true));
if (window.matchMedia){
  const mq = window.matchMedia("(prefers-color-scheme: dark)");
  const onSystem = () => { if (theme === "auto") themeListeners.forEach(fn => fn()); };
  if (mq.addEventListener) mq.addEventListener("change", onSystem);
}
themeListeners.push(() => viewer.repaint());

let startTheme = "dark";
try { startTheme = localStorage.getItem("maths-engine-theme") || "dark"; } catch (e) {}
applyTheme(startTheme === "light" ? "light" : startTheme === "auto" ? "auto" : "dark", false);

viewer.init();
initConstants();
initMagic();
initPrimes();
initBig();
initFractal();
initNumbers();
initPascal();

let startTool = location.hash.slice(1);
if (!TOOLS.includes(startTool)){
  try { startTool = localStorage.getItem("maths-engine-tool") || "pi"; } catch (e) { startTool = "pi"; }
}
showTool(startTool, true);
