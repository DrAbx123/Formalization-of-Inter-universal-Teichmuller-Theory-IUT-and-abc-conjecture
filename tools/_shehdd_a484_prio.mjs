import { readFileSync, existsSync, readdirSync, statSync } from 'node:fs';
const ROOT='D:/lean';
const prio=readFileSync(ROOT+'/dag/watchdog/priority-files.txt','utf8').split('\n').filter(Boolean);
const olean=f=>existsSync(ROOT+'/.lake/build/lib/lean/'+f.replace(/\.lean$/,'.olean'));
const green=prio.filter(olean), miss=prio.filter(f=>!olean(f));
console.log('priority green='+green.length+' missing='+miss.length);
for(const f of miss.slice(0,20)){
  const log='dag/watchdog/logs/'+f.replace(/\//g,'_')+'.log';
  const lp=ROOT+'/'+log;
  let err='';
  if(existsSync(lp)){ const t=readFileSync(lp,'utf8').split('\n').filter(l=>l.includes(': error')).slice(0,2); err=t.join(' || ').slice(0,300); }
  console.log('MISS '+f+' logerr='+(err?'YES: '+err:'none'));
}
