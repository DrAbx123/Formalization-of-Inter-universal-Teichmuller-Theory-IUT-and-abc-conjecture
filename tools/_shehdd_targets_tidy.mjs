import { readFileSync, writeFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const extra=ROOT+'/dag/watchdog/extra-targets.txt';
const cur=readFileSync(extra,'utf8').split('\n').map(l=>l.trim()).filter(Boolean);
const seen=new Set(); const nonP=[]; const pro=[];
for(const l of cur){ if(seen.has(l)) continue; seen.add(l); if(!existsSync(ROOT+'/'+l)) continue; if(l.includes('_AutoProbe_')) pro.push(l); else nonP.push(l); }
const out=[...nonP.sort(),...pro.sort()];
writeFileSync(extra,out.join('\n')+'\n');
console.log('targets='+out.length+' non_probe='+nonP.length+' auto_probe='+pro.length);
