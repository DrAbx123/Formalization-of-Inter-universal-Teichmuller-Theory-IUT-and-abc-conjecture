import { readFileSync, writeFileSync, existsSync } from 'node:fs';
const p='D:/lean/coord/DAG-BLOCKED.json';
let j={blocked:[]}; if(existsSync(p)){ try{ j=JSON.parse(readFileSync(p,'utf8')); }catch{} }
if(!Array.isArray(j.blocked)) j.blocked=[];
const add=(id,reason)=>{ if(!j.blocked.some(x=>x.id===id)) j.blocked.push({id,reason,kind:'PRAGMATIC-DEAD-END',recorded_by:'shehdd',at:new Date().toISOString()}); };
add('n8-legacy-tmp-pipeline','tmp/n8-20261018 (2258 lean,0 results) + tmp/n8-20261020 (113) + tmp/sheaf/n8 (878 lean,23 EXIT0/2 EXIT1/853 no-result) are archived old pipeline (no changes in last hour); Group1Statement.lean duplicates LeanFormal decls; fixing has no target-path value. Keep archived read-only (coord/N8-LEGACY-ARCHIVE.md).');
add('legacy-dag-fragment','coord/target-chain.legacy-dag.json (89 nodes/164 edges: PROVED 18, CONDITIONAL 18, GAP 15, NAMED 38) is historical; dag_next excludes legacy-dag: prefix; keep frozen, no new nodes.');
writeFileSync(p, JSON.stringify(j,null,2));
console.log('blocked entries='+j.blocked.length);
