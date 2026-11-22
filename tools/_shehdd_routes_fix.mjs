import { readFileSync, writeFileSync } from 'node:fs';
const p='D:/lean/coord/target-chain.routes.json';
const j=JSON.parse(readFileSync(p,'utf8'));
// fix betaTrack node id + edge ids (fragment-local ids must be unprefixed)
const b=(j.nodes||[]).find(x=>x.id==='routes:problemC_nested_betaTrack');
if(b){ b.id='problemC_nested_betaTrack'; }
for(const e of (j.edges||[])){
  if(e.from==='routes:problemC_nested_betaTrack') e.from='problemC_nested_betaTrack';
  if(e.to==='routes:problemC_nested') e.to='problemC_nested';
  if(e.from==='routes:problemC_nested') e.from='problemC_nested';
}
// note verification for problemC_nested
const n=(j.nodes||[]).find(x=>x.id==='problemC_nested');
if(n){ n.note = n.note.replace('PENDING-VERIFY: watchdog compile.','VERIFIED (shehdd): Mzk1NestedInductionBaseDischargedActual EXIT=0 in results log; probe EXIT0 pending.'); }
writeFileSync(p, JSON.stringify(j,null,2));
console.log('fixed betaTrack id/edges; problemC_nested note updated');
