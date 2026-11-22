import { readdirSync, readFileSync, writeFileSync, existsSync } from 'node:fs';
import { join } from 'node:path';
const ROOT='D:/lean'; const NODES=join(ROOT,'dag','nodes');
const files=readdirSync(NODES).filter(f=>f.endsWith('.json'));
const nodes=[]; const edges=[]; const statusMap={'kernel_closed':'PROVED','proof_body_checked':'PROVED','statement_compiles':'CONDITIONAL','existing_unrevalidated':'CONDITIONAL','open':'GAP'};
const kindMap={'statement':'theorem','definition':'interface','target':'target','milestone':'interface','computation':'theorem'};
for(const f of files){ let j; try{ j=JSON.parse(readFileSync(join(NODES,f),'utf8')); }catch{ continue; }
  const lid='legacy:'+j.id;
  const leanFile=j.lean&&j.lean.file; const decl=j.lean&&j.lean.declaration;
  const exists=leanFile?existsSync(join(ROOT,leanFile)):false;
  const fs=exists?[leanFile]:[]; const decls={};
  if(exists&&decl){ const parts=decl.split(/[\\/,\s]+/).filter(s=>s.length>0); const names=[];
    for(const p of parts){ const tail=p.split('.').pop(); if(tail&&/^[A-Za-z_][A-Za-z0-9_'!?]*$/.test(tail)&&!names.includes(tail)) names.push(tail); }
    if(names.length) decls[leanFile]=names.slice(0,6); }
  const status=statusMap[j.proof_status]||'NAMED';
  nodes.push({ id:lid, kind:kindMap[j.kind]||'theorem', title:(j.statement||j.id).slice(0,120), status,
    files:fs, declarations:decls, note:'legacy SHEAF DAG node; proof_status='+(j.proof_status||'?')+'; gaps: '+((j.gaps||[]).slice(0,2).join(' | ').slice(0,300)) });
}
for(const f of files){ let j; try{ j=JSON.parse(readFileSync(join(NODES,f),'utf8')); }catch{ continue; }
  const lid='legacy:'+j.id;
  for(const d of (j.statement_dependencies||[])) edges.push({ from:lid, to:'legacy:'+d, kind:'statement' });
  for(const d of (j.proof_dependencies||[])) edges.push({ from:lid, to:'legacy:'+d, kind:'proof' });
  for(const e of (j.edge_evidence||[])) if(e.kind==='statement'||e.kind==='proof') edges.push({ from:lid, to:'legacy:'+e.to, kind:e.kind });
}
const ids=new Set(nodes.map(n=>n.id)); const dropped=edges.filter(e=>!ids.has(e.from)||!ids.has(e.to)).length;
const okEdges=edges.filter(e=>ids.has(e.from)&&ids.has(e.to));
writeFileSync(join(ROOT,'coord','target-chain.legacy-dag.json'), JSON.stringify({ nodes, edges:okEdges }, null, 2));
console.log(JSON.stringify({ node_files:files.length, nodes:nodes.length, edges:okEdges.length, dropped_edges:dropped }, null, 2));