
import fs from "node:fs";
import path from "node:path";
import { execFileSync } from "node:child_process";
const root = "D:\\lean";
const buildDir = path.join(root, ".lake", "build", "lib", "lean");
function modToFile(mod) { return path.join(root, mod.replaceAll(".", "\\") + ".lean"); }
function modToOlean(mod) { return path.join(buildDir, mod.replaceAll(".", "\\") + ".olean"); }
const targets = process.argv.slice(2);
const missing = new Set(), visited = new Set();
function visit(mod) {
  if (visited.has(mod)) return; visited.add(mod);
  const f = modToFile(mod);
  if (!fs.existsSync(f)) { console.error("NOFILE " + mod); process.exit(2); }
  const txt = fs.readFileSync(f, "utf8");
  const deps = [];
  for (const line of txt.split(/\r?\n/)) {
    const m = line.match(/^import\s+(\S+)/);
    if (m && m[1].startsWith("tmp.")) deps.push(m[1]);
  }
  for (const d of deps) visit(d);
  if (!fs.existsSync(modToOlean(mod))) missing.add(mod);
}
for (const t of targets) visit(t);
// order: dependencies first (simple DFS postorder over missing set)
const order = [];
const done = new Set();
function emit(mod) {
  if (done.has(mod) || !missing.has(mod)) return;
  done.add(mod);
  const txt = fs.readFileSync(modToFile(mod), "utf8");
  const deps = [];
  for (const line of txt.split(/\r?\n/)) {
    const m = line.match(/^import\s+(\S+)/);
    if (m && m[1].startsWith("tmp.")) deps.push(m[1]);
  }
  for (const d of deps) emit(d);
  order.push(mod);
}
for (const t of targets) emit(t);
console.log("BUILD ORDER:");
for (const o of order) console.log("  " + o);
const t0 = Date.now();
for (const mod of order) {
  const leanFile = modToFile(mod).replaceAll("\\", "/");
  const olean = modToOlean(mod);
  console.log("=== compiling " + mod + " at " + ((Date.now()-t0)/1000).toFixed(1) + "s");
  try {
    const out = execFileSync(path.join(root, "lake.exe"), ["env","lean","-j1","-R",root,"-M","8192","-o",olean,leanFile], { cwd: root, encoding: "utf8", stdio: ["ignore","pipe","pipe"], timeout: 3600000 });
    if (out.trim()) console.log(out.slice(-3000));
    console.log("OK " + mod);
  } catch (e) {
    console.log("FAILED " + mod);
    if (e.stdout) console.log("STDOUT:\n" + String(e.stdout).slice(-6000));
    if (e.stderr) console.log("STDERR:\n" + String(e.stderr).slice(-6000));
    process.exit(1);
  }
}
console.log("ALL DONE in " + ((Date.now()-t0)/1000).toFixed(1) + "s");
