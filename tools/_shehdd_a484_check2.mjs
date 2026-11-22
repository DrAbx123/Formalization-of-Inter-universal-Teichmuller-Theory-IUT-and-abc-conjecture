import { readFileSync, existsSync, statSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const prio=readFileSync(ROOT+'/dag/watchdog/priority-files.txt','utf8').split('\n').filter(Boolean);
const queue=readFileSync(ROOT+'/dag/watchdog/extra-targets.txt','utf8').split('\n').filter(Boolean);
const olean=f=>existsSync(ROOT+'/.lake/build/lib/lean/'+f.replace(/\.lean$/,'.olean'));
console.log('priority='+prio.length+' green='+prio.filter(olean).length+' queue='+queue.length);
// DAG rebuild time and node count
const dag=ROOT+'/dag/declaration-dag.json';
if(existsSync(dag)){ const d=JSON.parse(readFileSync(dag,'utf8')); console.log('dag mtime='+statSync(dag).mtime.toISOString().slice(11,19)+' nodes='+(d.nodes?d.nodes.length:'?')+' edges='+(d.edges?d.edges.length:'?')); }
// newest olean times among tmp/sheaf/xif/paper
const dir=ROOT+'/.lake/build/lib/lean/tmp/sheaf/xif/paper';
if(existsSync(dir)){ const items=readdirSync(dir).filter(f=>f.endsWith('.olean')).map(f=>({f,t:statSync(dir+'/'+f).mtimeMs})).sort((a,b)=>b.t-a.t).slice(0,8); console.log('newest paper oleans:'); for(const i of items) console.log('  '+i.f.replace('.olean','')+' '+new Date(i.t).toISOString().slice(11,19)); }
// fresh failing logs (10 min)
const now=Date.now(); const fresh=[];
for(const f of readdirSync(ROOT+'/dag/watchdog/logs')){ const st=statSync(ROOT+'/dag/watchdog/logs/'+f); if(now-st.mtimeMs<10*60*1000) fresh.push(f); }
console.log('fresh logs='+fresh.length+': '+fresh.slice(0,10).join(', '));
