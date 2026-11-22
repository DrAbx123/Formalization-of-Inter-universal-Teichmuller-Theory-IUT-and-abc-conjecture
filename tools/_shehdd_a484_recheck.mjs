import { readFileSync, existsSync, statSync } from 'node:fs';
const ROOT='D:/lean';
const prio=readFileSync(ROOT+'/dag/watchdog/priority-files.txt','utf8').split('\n').filter(Boolean);
const queue=readFileSync(ROOT+'/dag/watchdog/extra-targets.txt','utf8').split('\n').filter(Boolean);
const olean=f=>existsSync(ROOT+'/.lake/build/lib/lean/'+f.replace(/\.lean$/,'.olean'));
console.log('priority='+prio.length+' green='+prio.filter(olean).length+' queue='+queue.length);
for(const f of prio.filter(f=>!olean(f))){
  const src=ROOT+'/'+f; const mt=existsSync(src)?statSync(src).mtime.toISOString().slice(11,19):'-';
  const log=ROOT+'/dag/watchdog/logs/'+f.replace(/\//g,'_')+'.log';
  const lt=existsSync(log)?statSync(log).mtime.toISOString().slice(11,19):'-';
  const firstErr=existsSync(log)?(readFileSync(log,'utf8').split('\n').find(l=>l.includes(': error'))||'').trim().slice(0,150):'';
  console.log('MISS '+f.split('/').pop()+' src='+mt+' log='+lt+' ownerActive='+(mt>lt)+' err='+firstErr);
}
