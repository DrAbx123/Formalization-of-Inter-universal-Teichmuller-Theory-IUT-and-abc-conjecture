import { readFileSync, writeFileSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/repo-route-index-data.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const logs=ROOT+'/dag/watchdog/logs';
const logFiles=new Set(readdirSync(logs));
let n=0;
for(const r of j.rows){
  if(r.citable!=='EXIT1') continue;
  if(r.index_note && !r.index_note.startsWith('EXIT1 (no inline error')) continue;
  const flat=r.file.split('/').join('_').split('\\').join('_').split(':').join('_');
  const cand=flat+'.lean.log';
  let logName=null;
  if(logFiles.has(cand)) logName=cand;
  else {
    const base=r.file.split('/').pop();
    for(const f of logFiles){ if(f.endsWith('_'+base+'.log')){ logName=f; break; } }
  }
  if(logName){ const ls=readFileSync(logs+'/'+logName,'utf8').split('\n'); let err=null; for(let i=ls.length-1;i>=0;i--){ if(ls[i].includes(': error')){ err=ls[i].trim(); break; } } if(err){ r.index_note='EXIT1 latest: '+err.slice(0,200); n++; } }
}
writeFileSync(p, JSON.stringify(j,null,2));
console.log('annotated from logs='+n);
