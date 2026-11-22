import { readFileSync, writeFileSync } from 'node:fs';
const p='D:/lean/coord/target-chain.routes.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const n=(j.nodes||[]).find(x=>x.id==='routes:problemC_nested');
if(n){
  n.note = n.note + ' VERIFIED (shehdd, results-log): Mzk1NestedInductionBaseDischargedActual EXIT=0; probe EXIT0 pending.';
  writeFileSync(p, JSON.stringify(j,null,2));
  console.log('note updated');
} else console.log('missing');
