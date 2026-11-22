import { readFileSync, writeFileSync, existsSync } from 'node:fs';
const p='D:/lean/coord/repo-route-index-data.json';
const j=JSON.parse(readFileSync(p,'utf8'));
let changed=0, stale=0, existingRed=0;
for(const r of j.rows){
  if(r.citable!=='EXIT1') continue;
  const f='D:/lean/'+r.file;
  if(!existsSync(f)){ r.citable='STALE_NO_SOURCE'; r.index_note='shehdd A460: source file absent in current tree (moved/archived); index row stale, not evidence of red'; changed++; stale++; }
  else { existingRed++; }
}
j.stats.citable.EXIT1=(j.stats.citable.EXIT1||0)-changed;
j.stats.citable.STALE_NO_SOURCE=(j.stats.citable.STALE_NO_SOURCE||0)+changed;
writeFileSync(p, JSON.stringify(j,null,2));
console.log('stale-marked='+stale+' existing-red='+existingRed+' EXIT1='+j.stats.citable.EXIT1);
