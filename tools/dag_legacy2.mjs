import { readdirSync, readFileSync, writeFileSync, existsSync } from 'node:fs';
import { join } from 'node:path';
const ROOT='D:/lean'; const NODES=join(ROOT,'dag','nodes');
const files=readdirSync(NODES).filter(f=>f.endsWith('.json'));
const statusMap={'kernel_closed':'PROVED','proof_body_checked':'PROVED','statement_compiles':'CONDITIONAL','existing_unrevalidated':'CONDITIONAL','open':'GAP'};
const kindMap={'statement':'theorem','definition':'interface','target':'target','milestone':'interface','computation':'theorem'};
const stop=new Set(['theorems','proof','pending','data','type','ofFields','U','Witness','and','or','left','right','definition','construction','exists','unitReferenceLog']);
const nodes=[]; const edges=[];
for(const f of files){ let j; try{ j=JSON.parse(readFileSync(join(NODES,f),'utf8')); }catch{ continue; }
  const lid='legacy:'+j.id; const leanFile=j.lean&&j.lean.file; const decl=j.lean&&j.lean.declaration;
  const exists=leanFile?existsSync(join(ROOT,leanFile)):false; const fs=exists?[leanFile]:[]; const decls={};
  if(exists&&decl){ const src=readFileSync(join(ROOT,leanFile),'utf8'); const parts=decl.split(/[\/,\s]+/).filter(s=>s.length>0); const names=[];
    for(const p of parts){ const tail=p.split('.').pop(); if(!tail||stop.has(tail)) continue; if(!/^[A-Za-z_][A-Za-z0-9_'!?]*$/.test(tail)) continue; if(!src.includes(tail)) continue; if(!names.includes(tail)) names.push(tail); }
    if(names.length) decls[leanFile]=names.slice(0,8); }
  nodes.push({ id:lid, kind:kindMap[j.kind]||'theorem', title:(j.statement||j.id).slice(0,120), status:statusMap[j.proof_status]||'NAMED', files:fs, declarations:decls, note:'legacy SHEAF DAG node; proof_status='+(j.proof_status||'?') });
}
const ids=new Set(nodes.map(n=>n.id)); const seen=new Set();
for(const f of files){ let j; try{ j=JSON.parse(readFileSync(join(NODES,f),'utf8')); }catch{ continue; } const lid='legacy:'+j.id;
  const add=(to,kind)=>{ const t='legacy:'+to; if(!ids.has(t)) return; const k=lid+'|'+t+'|'+kind; if(seen.has(k)) return; seen.add(k); edges.push({from:lid,to:t,kind}); };
  for(const d of (j.statement_dependencies||[])) add(d,'statement');
  for(const d of (j.proof_dependencies||[])) add(d,'proof');
  for(const e of (j.edge_evidence||[])) if(e.kind==='statement'||e.kind==='proof') add(e.to,e.kind); }
writeFileSync(join(ROOT,'coord','target-chain.legacy-dag.json'), JSON.stringify({ nodes, edges }, null, 2));
console.log(JSON.stringify({ node_files:files.length, nodes:nodes.length, edges:edges.length }, null, 2));