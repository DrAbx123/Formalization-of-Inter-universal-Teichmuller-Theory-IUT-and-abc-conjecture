import { readFileSync, writeFileSync, existsSync } from 'node:fs';
import { join } from 'node:path';
const ROOT='D:/lean'; const GEN=join(ROOT,'dag','generated');
const nodes=JSON.parse(readFileSync(join(GEN,'nodes-files.json'),'utf8')).nodes;
const edges=JSON.parse(readFileSync(join(GEN,'edges-imports.json'),'utf8')).edges;
const problems=[];
const ids=new Set(); for(const n of nodes){ if(ids.has(n.id)) problems.push('dup id '+n.id); ids.add(n.id); }
for(const e of edges){ if(!ids.has(e.from)) problems.push('edge from missing '+e.from); if(!ids.has(e.to)) problems.push('edge to missing '+e.to); }
// Kahn acyclicity
const indeg=new Map(), adj=new Map();
for(const n of nodes){ indeg.set(n.id,0); adj.set(n.id,[]); }
const ekeys=new Set(); let dupEdges=0;
for(const e of edges){ const k=e.from+'|'+e.to; if(ekeys.has(k)){dupEdges++;continue;} ekeys.add(k); adj.get(e.from).push(e.to); indeg.set(e.to,(indeg.get(e.to)||0)+1); }
const q=[]; for(const n of nodes) if((indeg.get(n.id)||0)===0) q.push(n.id);
let seen=0; for(let i=0;i<q.length;i++){ const v=q[i]; seen++; for(const w of adj.get(v)||[]){ indeg.set(w,indeg.get(w)-1); if(indeg.get(w)===0) q.push(w); } }
const cycle = seen!==nodes.length;
if(cycle) problems.push('file import graph cycle (topo seen '+seen+'/'+nodes.length+')');
// chain validation
let chainReport={nodes:0,edges:0,problems:[]};
const chainPath=join(ROOT,'dag','target-chain.json');
if(existsSync(chainPath)){ const chain=JSON.parse(readFileSync(chainPath,'utf8')); const cids=new Set();
  for(const n of chain.nodes||[]){ if(cids.has(n.id)) chainReport.problems.push('dup chain id '+n.id); cids.add(n.id);
    for(const f of n.files||[]) if(!existsSync(join(ROOT,f))) chainReport.problems.push('missing file '+f+' in '+n.id);
    for(const [f,decls] of Object.entries(n.declarations||{})){ const p=join(ROOT,f); if(!existsSync(p)){chainReport.problems.push('missing decl file '+f); continue;} const src=readFileSync(p,'utf8'); for(const d of decls) if(!src.includes(d)) chainReport.problems.push('decl not found '+d+' in '+f); }
    if(!['PROVED','BOTTOM','CONDITIONAL','NAMED','TREE_ASSET','DEF','GAP'].includes(n.status)) chainReport.problems.push('bad status '+n.status+' '+n.id);
    if(!['target','theorem','interface','tree_asset','bottom','conditional','bridge','named_input'].includes(n.kind)) chainReport.problems.push('bad kind '+n.kind+' '+n.id); }
  for(const e of chain.edges||[]){ chainReport.edges++; if(!cids.has(e.from)) chainReport.problems.push('chain from missing '+e.from); if(!cids.has(e.to)) chainReport.problems.push('chain to missing '+e.to); if(!['statement','proof','interface','gap'].includes(e.kind)) chainReport.problems.push('bad edge kind '+e.kind); }
  const cadj=new Map(); const cindeg=new Map(); for(const id of cids){cadj.set(id,[]);cindeg.set(id,0);}
  for(const e of chain.edges||[]){ cadj.get(e.from).push(e.to); cindeg.set(e.to,cindeg.get(e.to)+1); }
  const cq=[...cids].filter(id=>cindeg.get(id)===0); let cseen=0;
  for(let i=0;i<cq.length;i++){ const v=cq[i]; cseen++; for(const w of cadj.get(v)||[]){ cindeg.set(w,cindeg.get(w)-1); if(cindeg.get(w)===0) cq.push(w); } }
  if(cseen!==cids.size) chainReport.problems.push('chain cycle (topo '+cseen+'/'+cids.size+')');
  chainReport.nodes=cids.size; }
// Tarjan SCC to isolate cyclic components
const sccIndex=new Map(); const sccLow=new Map(); const sccOn=new Map(); const sccStack=[]; const sccs=[]; let sccCounter=0;
const sccEdges=new Map(); for(const e of edges){ if(!sccEdges.has(e.from)) sccEdges.set(e.from,[]); sccEdges.get(e.from).push(e.to); }
function strongconnect(v){ sccIndex.set(v,sccCounter); sccLow.set(v,sccCounter); sccCounter++; sccStack.push(v); sccOn.set(v,true);
  for(const w of sccEdges.get(v)||[]){ if(!sccIndex.has(w)){ strongconnect(w); sccLow.set(v,Math.min(sccLow.get(v),sccLow.get(w))); } else if(sccOn.get(w)){ sccLow.set(v,Math.min(sccLow.get(v),sccIndex.get(w))); } }
  if(sccLow.get(v)===sccIndex.get(v)){ const comp=[]; let w; do{ w=sccStack.pop(); sccOn.set(w,false); comp.push(w); }while(w!==v); sccs.push(comp); } }
for(const n of nodes) if(!sccIndex.has(n.id)) strongconnect(n.id);
const cyclicComps=sccs.filter(c=>c.length>1).map(c=>c.map(id=>id.replace('file:',''))).sort((a,b)=>b.length-a.length);
const cyclicNodes=new Set(cyclicComps.flat());
const cyclicWithOlean=nodes.filter(n=>cyclicNodes.has(n.path)&&n.olean_present).map(n=>n.path);
const chainFiles=(existsSync(join(ROOT,'dag','target-chain.json')))?JSON.parse(readFileSync(join(ROOT,'dag','target-chain.json'),'utf8')).nodes.flatMap(n=>n.files||[]):[];
const chainInCycles=chainFiles.filter(f=>cyclicNodes.has(f));
writeFileSync(join(ROOT,'dag','import-cycles.json'), JSON.stringify({ cyclic_scc_count:cyclicComps.length, cyclic_file_count:cyclicNodes.size, cyclic_with_olean:cyclicWithOlean, chain_files_in_cycles:chainInCycles, sccs:cyclicComps.slice(0,50) }, null, 2));
if(cyclicWithOlean.length>0) problems.push('cyclic components contain '+cyclicWithOlean.length+' files WITH olean');
if(chainInCycles.length>0) problems.push('curated chain files in import cycles: '+chainInCycles.join(','));
const summary=JSON.parse(readFileSync(join(GEN,'summary.json'),'utf8'));
const report={ generated_at:new Date().toISOString(),
  approach:'root-aware file-level fresh Lean DAG: every .lean file in the workspace is a node; imports resolved within the importer root first (repo root or a ported package root), then repo root, then other roots',
  file_graph:{ nodes:nodes.length, edges:[...ekeys].length, raw_edges:edges.length, duplicate_edges:dupEdges, import_cycle:cycle, problems:problems.length },
  curated_target_chain:chainReport, coverage:summary, cyclic_components:{ count:cyclicComps.length, files:cyclicNodes.size, sccs:cyclicComps.slice(0,100), with_olean:cyclicWithOlean },  validation:{ ok: problems.length===0 && chainReport.problems.length===0 } };
writeFileSync(join(ROOT,'dag','DAG-VALIDATION.json'),JSON.stringify(report,null,2));
console.log(JSON.stringify(report,null,2).slice(0,3200));
for(const p of problems.slice(0,10)) console.log('PROBLEM: '+p);
for(const p of chainReport.problems.slice(0,10)) console.log('CHAIN: '+p);