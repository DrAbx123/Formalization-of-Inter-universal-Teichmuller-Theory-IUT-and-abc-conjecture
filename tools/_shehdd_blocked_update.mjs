import { readFileSync, writeFileSync, existsSync } from 'node:fs';
const p='D:/lean/coord/DAG-BLOCKED.json';
let j={blocked:[]};
if(existsSync(p)){ try{ j=JSON.parse(readFileSync(p,'utf8')); }catch{} }
if(!Array.isArray(j.blocked)) j.blocked=[];
const add=(id,reason,kind)=>{ if(!j.blocked.some(x=>x.id===id)) j.blocked.push({id,reason,kind:kind||'PRAGMATIC-DEAD-END',recorded_by:'shehdd',at:new Date().toISOString()}); };
add('legacy-sourcepsi-olean-chain','n8 old-layout orphan tree (SourcePsiResidueRingFinite/…/UniformizerAbsorption/ReductionSpecialFiber/ReductionModelComparison/AdicCompletionFractionField) absent from current root; porting costs ~9 modules + ~50-file legacy compile and is not on target-chain path. PARKED per Lead A460.','PRAGMATIC-DEAD-END');
add('legacy-tmp-red-rows','11 repo-route-index EXIT1 rows all point to absent tmp/*.lean sources (stale index) → marked STALE_NO_SOURCE in index; no proof work possible.','PRAGMATIC-DEAD-END');
writeFileSync(p, JSON.stringify(j,null,2));
console.log('blocked entries='+j.blocked.length);
