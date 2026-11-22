import { readFileSync, existsSync, statSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const prio=readFileSync(ROOT+'/dag/watchdog/priority-files.txt','utf8').split('\n').filter(Boolean);
const queue=readFileSync(ROOT+'/dag/watchdog/extra-targets.txt','utf8').split('\n').filter(Boolean);
const olean=f=>existsSync(ROOT+'/.lake/build/lib/lean/'+f.replace(/\.lean$/,'.olean'));
console.log('priority='+prio.length+' green='+prio.filter(olean).length+' queue='+queue.length);
const now=Date.now();
const fresh=[];
for(const f of readdirSync(ROOT+'/dag/watchdog/logs')){
  const st=statSync(ROOT+'/dag/watchdog/logs/'+f);
  if(now-st.mtimeMs < 12*60*1000) fresh.push({f,mt:st.mtimeMs});
}
fresh.sort((a,b)=>b.mt-a.mt);
console.log('fresh logs (12min)='+fresh.length);
for(const {f} of fresh.slice(0,20)){
  const txt=readFileSync(ROOT+'/dag/watchdog/logs/'+f,'utf8');
  const errs=txt.split('\n').filter(l=>l.includes(': error')).slice(0,2);
  console.log('  '+f.replace('.lean.log','')+' | errs='+errs.length);
  for(const e of errs) console.log('      '+e.trim().slice(0,200));
}
