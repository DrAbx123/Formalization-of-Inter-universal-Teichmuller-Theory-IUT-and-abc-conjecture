import { readFileSync, writeFileSync } from 'node:fs';
const ROOT='D:/lean';
const dag=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const nodes=dag.nodes, edges=dag.edges;
const byId=new Map(nodes.map(n=>[n.id,n]));
const IMPL=/(Actual|Consumer|Rollup|Cluster|Witness|Green|Bundle|Joint|bookkeeping|Mzk1|S3[0-9]|Probe|Reduction|Adapter|Index|Coordination|Transport|Comparison|Laws|Statement|Interface|Rows)/;
const KEEP_KINDS=new Set(['target','theorem','conditional','bottom','bridge','named_input','def','gap']);
const REGION_OK=(id)=>{
  if(/^(T[0-6]-|B[0-9]|N[0-9]|D$|Dbridge|D-)/.test(id)) return true;
  if(id.startsWith('iut-skeleton:')) return true;
  if(/^iutiv-abc:(G[0-9]|G[0-9]\.|HW|IUTIV|StepXI|E5|GapReduction|G0|G2|G3)/.test(id)) return true;
  if(/^iutiii:(IUTIII|Cor|Theorem|HULL|STEPXI|COR312)/.test(id)) return true;
  if(/^theta-etth:(A[0-9]|P58|SAT|X[0-9])/.test(id)) return true;
  if(/^e-deep:E[1-5]/.test(id)) return true;
  if(/^iuti-ii:(Section0|IUTII|HodgeTheta)/.test(id)) return true;
  if(/^foundation:(GATE|B[0-9]|C\.|D\.)/.test(id)) return true;
  if(/^mainline:/.test(id)) return true;
  if(/^routes:(problem|four|theta|stage|theorem)/.test(id)) return true;
  return false;
};
const sel=nodes.filter(n=>KEEP_KINDS.has(n.kind) && REGION_OK(n.id) && (!IMPL.test(n.id) || n.id.startsWith('iut-skeleton:') || /^theta-etth:A/.test(n.id) || /^iutiv-abc:G/.test(n.id) || /^e-deep:E[1-5]/.test(n.id)));
const selIds=new Set(sel.map(n=>n.id));
const out=new Map(); for(const n of nodes) out.set(n.id,[]); for(const e of edges){ if(out.has(e.from)) out.get(e.from).push(e); }
function collapse(start){
  // BFS through non-selected nodes; return first-hop edges reaching selected nodes
  const res=new Map(); const stack=out.get(start.id).map(e=>({e,depth:1})); const seen=new Set();
  for(const x of stack){ if(seen.has(x.e.to+'|'+x.e.kind)) continue; seen.add(x.e.to+'|'+x.e.kind); if(selIds.has(x.e.to)){ res.set(x.e.to+'|'+x.e.kind,{from:start.id,to:x.e.to,kind:x.e.kind,evidence:x.e.evidence||'planned',collapsed:x.depth>1}); } else if(x.depth<6){ for(const e2 of (out.get(x.e.to)||[])) stack.push({e:e2,depth:x.depth+1}); } }
  return [...res.values()];
}
const tEdges=[]; const seen=new Set();
for(const n of sel){ for(const e of collapse(n)){ const k=e.from+'|'+e.to+'|'+e.kind; if(seen.has(k)) continue; seen.add(k); tEdges.push(e); } }
// ensure undirected connectivity of theorem graph by linking components to largest
const adj=new Map(); for(const n of sel) adj.set(n.id,[]); for(const e of tEdges){ adj.get(e.from)?.push(e.to); adj.get(e.to)?.push(e.from); }
const comp=new Map(); let comps=0; for(const n of sel){ if(comp.has(n.id)) continue; comps++; const st=[n.id]; comp.set(n.id,comps); while(st.length){ const u=st.pop(); for(const v of (adj.get(u)||[])){ if(!comp.has(v)){ comp.set(v,comps); st.push(v); } } } }
if(comps>1){ const groups=new Map(); for(const n of sel){ const c=comp.get(n.id); if(!groups.has(c)) groups.set(c,[]); groups.get(c).push(n.id); } const main=[...groups.entries()].sort((a,b)=>b[1].length-a[1].length)[0][0]; for(const [c,ids] of groups){ if(c===main) continue; tEdges.push({from:ids[0],to:groups.get(main)[0],kind:'hierarchy',visible:false,note:'connectivity only'}); } }
// break cycles: keep first edges, drop back-edges (recorded)
const ids2=new Set(sel.map(n=>n.id));
const adj2=new Map(); for(const id of ids2) adj2.set(id,[]); for(const e of tEdges){ if(!adj2.has(e.from)) adj2.set(e.from,[]); adj2.get(e.from).push(e); }
const state2=new Map(); const kept=[]; const dropped=[];
const dfs2=(u)=>{ state2.set(u,1); for(const e of (adj2.get(u)||[])){ if(!ids2.has(e.to)) continue; const s=state2.get(e.to)||0; if(s===1){ dropped.push(e); continue; } if(s===0) dfs2(e.to); kept.push(e); } state2.set(u,2); };
for(const id of ids2) if(!(state2.get(id))) dfs2(id);
tEdges.length=0; for(const e of kept) tEdges.push(e);
const outObj={generated_at:new Date().toISOString(),dropped_cycle_edges:dropped.length,level:'theorem',policy:'nodes are mathematical theorem/definition statements (paper/formal semantic ids), implementation/file-bookkeeping nodes excluded; edges statement/proof with evidence, collapsed through non-theorem nodes; hierarchy edges are connectivity-only',nodes:sel.map(n=>({id:n.id,kind:n.kind,status:n.status,title:n.title||'',files:(n.files||[]).slice(0,3),note:(n.note||'').slice(0,160)})),edges:tEdges};
writeFileSync(ROOT+'/dag/THEOREM-DAG.json', JSON.stringify(outObj,null,2));
const md=['# Theorem-level DAG','', 'generated: '+outObj.generated_at,'', 'nodes: '+sel.length+', edges: '+tEdges.length,'','| id | kind | status | title |','|---|---|---|---|'];
for(const n of sel) md.push('| '+n.id+' | '+n.kind+' | '+n.status+' | '+(n.title||'').replace(/\|/g,'/').slice(0,80)+' |');
writeFileSync(ROOT+'/dag/THEOREM-DAG.md', md.join('\n'));
console.log(JSON.stringify({nodes:sel.length,edges:tEdges.length,components_before:comps,dropped_cycles:dropped.length}));