import { readFileSync, writeFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/repo-route-index-data.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const lines=readFileSync(ROOT+'/tmp/xif_guarded_results.log','utf8').split('\n');
let n=0;
for(const r of j.rows){
  if(r.citable!=='EXIT1') continue;
  const base=r.file.split('/').pop();
  let err=null;
  for(let i=lines.length-1;i>=0;i--){ const l=lines[i]; if(l.includes(base) && l.includes(': error')){ err=l.trim(); break; } }
  if(err){ const msg=err.slice(0,190); r.index_note='EXIT1 latest: '+msg; n++; }
  else { r.index_note='EXIT1 (no inline error found; see dag/watchdog/logs)'; n++; }
}
writeFileSync(p, JSON.stringify(j,null,2));
console.log('red rows annotated='+n);
