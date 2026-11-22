import { readFileSync, writeFileSync, existsSync } from 'node:fs';
import { join } from 'node:path';
import { createHash } from 'node:crypto';
const ROOT='D:/lean'; const p=join(ROOT,'dag','declaration-dag.json');
const d=JSON.parse(readFileSync(p,'utf8'));
const problems=[]; const info=[]; const ids=new Set();
for(const n of d.nodes){ if(ids.has(n.id)) problems.push('dup id '+n.id); ids.add(n.id);
  for(const f of n.files||[]) if(!existsSync(join(ROOT,f))) problems.push('missing file '+f+' in '+n.id);
  for(const [f,decls] of Object.entries(n.declarations||{})){ const fp=join(ROOT,f); if(!existsSync(fp)){ problems.push('missing decl file '+f); continue; } const src=readFileSync(fp,'utf8'); for(const name of decls) if(!src.includes(name)) problems.push('decl not found '+name+' in '+f+' ('+n.id+')'); }
  if(!['PROVED','BOTTOM','CONDITIONAL','NAMED','TREE_ASSET','DEF','GAP','EXTERNAL'].includes(n.status)) problems.push('bad status '+n.status+' '+n.id);
  if(!['target','theorem','interface','tree_asset','bottom','conditional','bridge','named_input','route_mention','paper_label','web_route','gap','route','def'].includes(n.kind)) problems.push('bad kind '+n.kind+' '+n.id); }
const proofEdges=[]; const statementEdges=[];
for(const e of d.edges){ if(!ids.has(e.from)) problems.push('edge from missing '+e.from); if(!ids.has(e.to)) problems.push('edge to missing '+e.to); if(!['statement','proof','interface','gap','hierarchy'].includes(e.kind)) problems.push('bad edge kind '+e.kind); if(ids.has(e.from)&&ids.has(e.to)){ if(e.kind==='statement') statementEdges.push(e); else if(e.kind==='proof') proofEdges.push(e); } }
const checkAcyclic=(edges,label)=>{ const adj=new Map(), indeg=new Map(); for(const id of ids){adj.set(id,[]);indeg.set(id,0);} for(const e of edges){adj.get(e.from).push(e.to);indeg.set(e.to,indeg.get(e.to)+1);} const q=[...ids].filter(id=>indeg.get(id)===0); let seen=0; for(let i=0;i<q.length;i++){const v=q[i];seen++;for(const w of adj.get(v)){indeg.set(w,indeg.get(w)-1);if(indeg.get(w)===0)q.push(w);}} return {seen, total:ids.size, cyclic:seen!==ids.size, label}; };
const proofAcyc=checkAcyclic(proofEdges,'proof+interface');
const stmtAcyc=checkAcyclic(statementEdges,'statement');
if(proofAcyc.cyclic) problems.push('proof/interface subgraph has cycle: topo '+proofAcyc.seen+'/'+proofAcyc.total);
if(stmtAcyc.cyclic) info.push('statement/citation subgraph has cycle: topo '+stmtAcyc.seen+'/'+stmtAcyc.total+' (paper citation graph; informational)');
const byStatus={}; for(const n of d.nodes) byStatus[n.status]=(byStatus[n.status]||0)+1;
const byKind={}; for(const n of d.nodes) byKind[n.kind]=(byKind[n.kind]||0)+1;
const report={ generated_at:new Date().toISOString(), file:'dag/declaration-dag.json', source:createHash('sha256').update(readFileSync(p)).digest('hex'), nodes:d.nodes.length, edges:d.edges.length, proof_edges:proofEdges.length, statement_edges:statementEdges.length, merged_from:d.merged_from, merge_conflicts:(d.conflicts||[]).length, by_status:byStatus, by_kind:byKind, acyclicity:{proof:proofAcyc, statement:stmtAcyc}, info, problems, validation:{ ok: problems.length===0 } };
writeFileSync(join(ROOT,'dag','DECLARATION-DAG-VALIDATION.json'), JSON.stringify(report,null,2));
console.log(JSON.stringify({nodes:report.nodes, edges:report.edges, ok:report.validation.ok, problems:problems.length, info, proof:proofAcyc, statement:{cyclic:stmtAcyc.cyclic}},null,2));
for(const pr of problems.slice(0,12)) console.log('PROBLEM: '+pr);