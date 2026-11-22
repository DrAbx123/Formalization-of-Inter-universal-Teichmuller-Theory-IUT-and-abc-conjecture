
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { spawn } from 'node:child_process';

const PLAN = JSON.parse(fs.readFileSync('D:/lean/tmp/local-cft-port/_s2091_plan.json','utf8'));
const OUT = 'D:/lean/.lake/build/lib/lean';
const PORT = 'D:/lean/tmp/local-cft-port/local-class-field-theory-main';
const CKT = 'D:/lean/tmp/local-cft-port/continuous-kummer-theory-main';
const LOGDIR = 'D:/lean/tmp/local-cft-port/_s2091_logs';
const TSV = 'D:/lean/tmp/local-cft-port/_s2091_build.tsv';
const RAW = 'D:/lean/tmp/local-cft-port/_s2091_build.raw.log';
const THROTTLE = Number(process.env.THROTTLE || 6);
fs.mkdirSync(LOGDIR, { recursive: true });

const leanPath = [
  'D:/lean/.lake/packages/Cli/.lake/build/lib/lean',
  'D:/lean/.lake/packages/batteries/.lake/build/lib/lean',
  'D:/lean/.lake/packages/Qq/.lake/build/lib/lean',
  'D:/lean/.lake/packages/aesop/.lake/build/lib/lean',
  'D:/lean/.lake/packages/proofwidgets/.lake/build/lib/lean',
  'D:/lean/.lake/packages/importGraph/.lake/build/lib/lean',
  'D:/lean/.lake/packages/LeanSearchClient/.lake/build/lib/lean',
  'D:/lean/.lake/packages/plausible/.lake/build/lib/lean',
  'D:/lean/.lake/packages/mathlib/.lake/build/lib/lean',
  'D:/lean/.lake/build/lib/lean',
  OUT,
].join(';');

const order = PLAN.order;
const deps = PLAN.deps;
const fileOf = PLAN.fileOf;
const srcOf = (m) => fileOf[m].replace(/\\/g, '/');
const outOf = (m) => path.join(OUT, m.replace(/\./g, '/') + '.olean');
const sha = (f) => crypto.createHash('sha256').update(fs.readFileSync(f)).digest('hex').toUpperCase();
const log = (s) => fs.appendFileSync(RAW, s + '\n');

const done = new Set();
const fail = new Map();
for (const m of order) {
  const o = outOf(m);
  if (fs.existsSync(o) && fs.statSync(o).isFile()) done.add(m);
}
log('NODESTART3 ' + new Date().toISOString() + ' total=' + order.length + ' prebuilt=' + done.size);

function runOne(m) {
  return new Promise((resolve) => {
    const src = srcOf(m);
    const root = src.startsWith(CKT + '/') ? CKT : PORT;
    const out = outOf(m);
    fs.mkdirSync(path.dirname(out), { recursive: true });
    const errFile = path.join(LOGDIR, m + '.log');
    const fd = fs.openSync(errFile, 'w');
    const t0 = Date.now();
    const child = spawn(process.env.LEAN_EXE || 'lean', ['-DmaxHeartbeats=4000000', '--root', root, '-o', out, src], {
      env: { ...process.env, LEAN_PATH: leanPath },
      stdio: ['ignore', fd, fd],
    });
    const timer = setTimeout(() => { try { child.kill('SIGKILL'); } catch {} }, 20 * 60 * 1000);
    child.on('exit', (code) => { clearTimeout(timer); try { fs.closeSync(fd); } catch {} resolve({ code, sec: ((Date.now()-t0)/1000).toFixed(1) }); });
    child.on('error', (e) => { clearTimeout(timer); try { fs.closeSync(fd); } catch {} resolve({ code: -1, sec: '0', err: String(e) }); });
  });
}

while (true) {
  const pending = order.filter((m) => !done.has(m) && !fail.has(m));
  if (pending.length === 0) break;
  const ready = pending.filter((m) => deps[m].every((d) => done.has(d) || !fileOf[d]));
  if (ready.length === 0) { for (const m of pending) fail.set(m, 'BLOCKED'); break; }
  const batch = ready.slice(0, THROTTLE);
  const results = await Promise.all(batch.map((m) => runOne(m).then((r) => [m, r])));
  for (const [m, r] of results) {
    if (r.code === 0) {
      done.add(m);
      const out = outOf(m);
      fs.appendFileSync(TSV, [m, 'EXIT=0', 'SEC=' + r.sec, 'OLEAN_BYTES=' + (fs.existsSync(out) ? fs.statSync(out).size : -1), 'OLEAN_SHA256=' + (fs.existsSync(out) ? sha(out) : 'NONE'), 'SRC_SHA256=' + sha(srcOf(m))].join('\t') + '\n');
    } else {
      fail.set(m, 'FAIL');
      fs.appendFileSync(TSV, [m, 'EXIT=FAIL', 'SEC=' + r.sec, 'SRC_SHA256=' + sha(srcOf(m))].join('\t') + '\n');
      log('FAILED ' + m + ' code=' + r.code);
    }
  }
  log('ROUND ' + new Date().toISOString() + ' done=' + done.size + ' fail=' + fail.size);
}
log('ALLDONE ' + new Date().toISOString() + ' done=' + done.size + ' fail=' + fail.size);
for (const [m, why] of fail) log('FAILEDMOD ' + m + ' ' + why);
