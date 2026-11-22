
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { spawn } from 'node:child_process';

const PORT = 'D:/lean/tmp/local-cft-port';
const DST = PORT + '/Brauer';
const OUT = 'D:/lean/.lake/build/lib/lean';
const LOGDIR = PORT + '/_m2b_logs';
const TSV = PORT + '/_m2b_build.tsv';
const RAW = PORT + '/_m2b_build.raw.log';
const TARGET = process.env.TARGET || 'Brauer.ArtinTransfer';
const THROTTLE = Number(process.env.THROTTLE || 2);
const LEAN_EXE = process.env.LEAN_EXE || 'C:/Users/Administrator/.elan/toolchains/leanprover--lean4---v4.32.2/bin/lean.exe';
const EXTRA_ARGS = (process.env.LEAN_ARGS || '').split(' ').filter(Boolean);
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
  'C:/Users/Administrator/.elan/toolchains/leanprover--lean4---v4.32.2/lib/lean',
].join(';');

const files = fs.readdirSync(DST).filter((f) => f.endsWith('.lean'));
const modOf = (f) => 'Brauer.' + f.replace(/\.lean$/, '');
const fileOf = {};
const deps = {};
for (const f of files) {
  const m = modOf(f);
  fileOf[m] = DST + '/' + f;
  deps[m] = fs.readFileSync(fileOf[m], 'utf8').split(/\r?\n/)
    .filter((l) => l.startsWith('import ')).map((l) => l.slice(7).trim());
}
const outOf = (m) => path.join(OUT, m.replace(/\./g, '/') + '.olean');
const sha = (f) => crypto.createHash('sha256').update(fs.readFileSync(f)).digest('hex').toUpperCase();
const log = (s) => fs.appendFileSync(RAW, s + '\n');

function closure(target) {
  const seen = new Set(); const st = [target];
  while (st.length) { const m = st.pop(); if (seen.has(m)) continue; seen.add(m); for (const d of deps[m] ?? []) if (deps[d]) st.push(d); }
  return seen;
}
const ALL = process.env.ALL === '1';
const cl = ALL ? new Set(Object.keys(deps)) : closure(TARGET);
const order = []; const state = {};
function visit(m) {
  if (state[m] === 2) return;
  if (state[m] === 1) throw new Error('import cycle at ' + m);
  state[m] = 1;
  for (const d of deps[m] ?? []) if (deps[d]) visit(d);
  state[m] = 2; order.push(m);
}
for (const m of (ALL ? Object.keys(deps) : [TARGET])) visit(m);
const localOrder = order.filter((m) => cl.has(m));

// external olean preflight
const extMissing = [];
for (const m of localOrder) for (const d of deps[m] ?? []) {
  if (deps[d]) continue;
  if (!leanPath.split(';').some((p) => fs.existsSync(path.join(p, d.replace(/\./g, '/') + '.olean')))) extMissing.push(d + ' (needed by ' + m + ')');
}
if (extMissing.length) {
  console.log('EXTERNAL_OLEAN_MISSING'); for (const x of extMissing) console.log(x);
  process.exit(3);
}

const results = [];
const failed = new Map();
const done = new Set();
for (const m of localOrder) {
  const o = outOf(m);
  if (fs.existsSync(o) && fs.statSync(o).mtimeMs >= fs.statSync(fileOf[m]).mtimeMs) done.add(m);
}
log('START ' + new Date().toISOString() + ' target=' + TARGET + ' all=' + (process.env.ALL === '1') + ' closure=' + localOrder.length + ' prebuilt=' + done.size);
console.log('plan ' + localOrder.join(' -> '));
console.log('prebuilt ' + [...done].join(','));

function runOne(m, attempt) {
  return new Promise((resolve) => {
    const src = fileOf[m];
    const out = outOf(m);
    fs.mkdirSync(path.dirname(out), { recursive: true });
    const errFile = path.join(LOGDIR, m + (attempt > 1 ? '.retry' + attempt : '') + '.log');
    const fd = fs.openSync(errFile, 'w');
    const t0 = Date.now();
    const args = [...EXTRA_ARGS, '--root', PORT, '-o', out, src];
    const child = spawn(LEAN_EXE, args, {
      env: { ...process.env, LEAN_PATH: leanPath },
      stdio: ['ignore', fd, fd],
    });
    const timer = setTimeout(() => { try { child.kill('SIGKILL'); } catch {} }, 30 * 60 * 1000);
    child.on('exit', (code) => {
      clearTimeout(timer); try { fs.closeSync(fd); } catch {}
      resolve({ code, sec: ((Date.now() - t0) / 1000).toFixed(1), log: errFile });
    });
    child.on('error', (e) => {
      clearTimeout(timer); try { fs.closeSync(fd); } catch {}
      resolve({ code: -1, sec: '0', err: String(e), log: errFile });
    });
  });
}
const transient = (txt) => /failed to (open|read|parse|load)[^\n]*\.olean|cannot open[^\n]*\.olean|error loading[^\n]*olean|invalid header[^\n]*olean|unexpected end of file|input file[^\n]*\.olean[^\n]*(missing|not found)|No such file or directory[^\n]*\.olean/i.test(txt);

// batch schedule
let round = 0;
while (true) {
  const pending = localOrder.filter((m) => !done.has(m) && !failed.has(m));
  if (pending.length === 0) break;
  const ready = pending.filter((m) => (deps[m] ?? []).every((d) => !deps[d] || done.has(d)));
  if (ready.length === 0) { for (const m of pending) failed.set(m, 'BLOCKED_DEPS'); break; }
  const batch = ready.slice(0, THROTTLE);
  round++;
  log('ROUND ' + round + ' ' + new Date().toISOString() + ' batch=' + batch.join(','));
  const rs = await Promise.all(batch.map(async (m) => {
    let attempt = 0, r;
    while (true) {
      attempt++;
      r = await runOne(m, attempt);
      if (r.code === 0) break;
      const txt = fs.existsSync(r.log) ? fs.readFileSync(r.log, 'utf8') : '';
      if (attempt <= 6 && (r.code === -1 || transient(txt))) {
        log('RETRY ' + m + ' attempt=' + attempt + ' code=' + r.code + ' transient=1');
        await new Promise((res) => setTimeout(res, 3000));
        continue;
      }
      break;
    }
    return { m, ...r, attempt };
  }));
  for (const r of rs) {
    const m = r.m;
    const srcSha = sha(fileOf[m]);
    if (r.code === 0 && fs.existsSync(outOf(m))) {
      done.add(m);
      const o = outOf(m);
      const row = [m, 'EXIT=0', 'SEC=' + r.sec, 'ATTEMPT=' + r.attempt, 'OLEAN_BYTES=' + fs.statSync(o).size, 'OLEAN_SHA256=' + sha(o), 'SRC_SHA256=' + srcSha, 'SRC=' + fileOf[m], 'OLEAN=' + o];
      fs.appendFileSync(TSV, row.join('\t') + '\n');
      results.push({ module: m, exit: 0, sec: r.sec, attempt: r.attempt, srcSha, olean: o, oleanSha: sha(o), bytes: fs.statSync(o).size });
      console.log('OK ' + m + ' sec=' + r.sec + ' attempt=' + r.attempt + ' olean=' + fs.statSync(o).size);
      log('OK ' + m + ' ' + row.join(' '));
    } else {
      failed.set(m, 'EXIT=' + r.code);
      const txt = fs.existsSync(r.log) ? fs.readFileSync(r.log, 'utf8') : (r.err || '(no log)');
      fs.appendFileSync(TSV, [m, 'EXIT=FAIL', 'CODE=' + r.code, 'SEC=' + r.sec, 'ATTEMPT=' + r.attempt, 'SRC_SHA256=' + srcSha, 'LOG=' + r.log].join('\t') + '\n');
      results.push({ module: m, exit: r.code, sec: r.sec, attempt: r.attempt, srcSha, log: r.log, output: txt });
      console.log('FAIL ' + m + ' code=' + r.code + ' log=' + r.log);
      log('----- OUTPUT ' + m + ' -----\n' + txt);
    }
  }
}
log('ALLDONE ' + new Date().toISOString() + ' done=' + done.size + ' fail=' + failed.size);
for (const [m, why] of failed) log('FAILEDMOD ' + m + ' ' + why);
fs.writeFileSync(PORT + '/_m2b_results.json', JSON.stringify({ target: TARGET, order: localOrder, results, failed: [...failed.entries()] }, null, 2));
console.log('DONE done=' + done.size + ' fail=' + failed.size);
for (const [m, why] of failed) console.log('FAILEDMOD ' + m + ' ' + why);
