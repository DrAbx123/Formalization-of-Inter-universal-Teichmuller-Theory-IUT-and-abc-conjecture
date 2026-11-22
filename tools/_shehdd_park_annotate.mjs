import { readFileSync, writeFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/repo-route-index-data.json';
const j=JSON.parse(readFileSync(p,'utf8'));
let n=0;
for(const r of j.rows){
  if(!r.file.includes('SourcePsi')) continue;
  if(r.citable==='EXIT1'){ r.index_note=(r.index_note||'')+' | PARKED legacy chain: Lead A460 PRAGMATIC-DEAD-END (n8 old-layout deps absent; repair = ~9 module port + ~50-file legacy compile, not target-chain path)'; n++; }
}
// ensure index metadata notes the park
j.parked_note='SourcePsi legacy chain rows are PARKED per Lead A460 (see coord/DAG-BLOCKED.json legacy-sourcepsi-olean-chain).';
writeFileSync(p, JSON.stringify(j,null,2));
console.log('parked-annotated rows='+n);
