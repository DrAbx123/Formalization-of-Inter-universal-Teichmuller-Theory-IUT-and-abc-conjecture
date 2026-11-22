import { readFileSync, existsSync, statSync } from 'node:fs';
const ROOT='D:/lean';
const prio=readFileSync(ROOT+'/dag/watchdog/priority-files.txt','utf8').split('\n').filter(Boolean);
const olean=f=>existsSync(ROOT+'/.lake/build/lib/lean/'+f.replace(/\.lean$/,'.olean'));
console.log('priority green='+prio.filter(olean).length+'/'+prio.length);
for(const f of prio.filter(f=>!olean(f))){
  const src=ROOT+'/'+f; const mt=existsSync(src)?statSync(src).mtime.toISOString().slice(11,19):'-';
  const log=ROOT+'/dag/watchdog/logs/'+f.replace(/\//g,'_')+'.log';
  let errs=[], lt='-';
  if(existsSync(log)){ const t=readFileSync(log,'utf8').split('\n').filter(l=>l.includes(': error')); errs=t.slice(0,2); lt=statSync(log).mtime.toISOString().slice(11,19); }
  console.log('MISS '+f.split('/').pop()+' src_mtime='+mt+' logtime='+lt+' errlines='+errs.length);
  for(const e of errs) console.log('    '+e.trim().slice(0,200));
}
