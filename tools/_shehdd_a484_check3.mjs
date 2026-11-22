import { readFileSync, existsSync, statSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const prio=readFileSync(ROOT+'/dag/watchdog/priority-files.txt','utf8').split('\n').filter(Boolean);
const queue=readFileSync(ROOT+'/dag/watchdog/extra-targets.txt','utf8').split('\n').filter(Boolean);
const olean=f=>existsSync(ROOT+'/.lake/build/lib/lean/'+f.replace(/\.lean$/,'.olean'));
console.log('priority='+prio.length+' green='+prio.filter(olean).length+' queue='+queue.length);
for(const f of prio.filter(f=>!olean(f))) console.log('MISS '+f);
const now=Date.now();
const fresh=[];
for(const f of readdirSync(ROOT+'/dag/watchdog/logs')){ const st=statSync(ROOT+'/dag/watchdog/logs/'+f); if(now-st.mtimeMs<8*60*1000) fresh.push({f,mt:st.mtimeMs}); }
fresh.sort((a,b)=>b.mt-a.mt);
console.log('fresh logs='+fresh.length);
for(const x of fresh.slice(0,12)){
  const t=readFileSync(ROOT+'/dag/watchdog/logs/'+x.f,'utf8').split('\n').filter(l=>l.includes(': error'));
  console.log('  '+x.f.replace('.lean.log','')+' errs='+t.length+(t.length?' | '+t[0].trim().slice(0,160):''));
}
