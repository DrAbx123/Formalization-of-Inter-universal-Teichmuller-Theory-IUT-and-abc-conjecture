import { readFileSync, existsSync, readdirSync, statSync } from 'node:fs';
const ROOT='D:/lean';
const q=readFileSync(ROOT+'/dag/watchdog/extra-targets.txt','utf8').split('\n').filter(Boolean);
const tak=q.filter(f=>f.startsWith('tmp/sheaf/takkun/'));
console.log('takkun queued='+tak.length);
console.log('=== takkun logs ===');
const logdir=ROOT+'/dag/watchdog/logs';
const logs=readdirSync(logdir).filter(f=>f.includes('takkun'));
console.log('takkun logs='+logs.length);
for(const f of logs.slice(-15)){
  const txt=readFileSync(logdir+'/'+f,'utf8');
  const errs=txt.split('\n').filter(l=>l.includes(': error')||l.toLowerCase().includes('out of memory')||l.toLowerCase().includes('oom')||l.toLowerCase().includes('heartbeats'));
  const stat=statSync(logdir+'/'+f);
  console.log(f.replace('.lean.log','')+' logtime='+new Date(stat.mtimeMs).toISOString().slice(11,19)+' errs='+errs.length+(errs.length?' | '+errs[0].trim().slice(0,220):''));
}
// olean count takkun ported
const p=ROOT+'/tmp/sheaf/takkun';
if(existsSync(p)){ function walk(x,acc){ for(const e of readdirSync(x,{withFileTypes:true})){ const s=x+'/'+e.name; if(e.isDirectory()) walk(s,acc); else if(e.name.endsWith('.lean')) acc.push(s); } return acc; } const files=walk(p,[]); const ole=files.filter(f=>existsSync(ROOT+'/.lake/build/lib/lean/'+f.replace(ROOT+'/','').replace(/\.lean$/,'.olean'))); console.log('takkun ported files='+files.length+' olean='+ole.length); }
