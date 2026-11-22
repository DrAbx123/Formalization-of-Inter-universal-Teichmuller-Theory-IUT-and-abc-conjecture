import { readFileSync, writeFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const dag=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const ATTACH=process.env.DAG_CLEAN_ATTACH!=='0';
const FALLBACK=process.env.DAG_FALLBACK==='1';
const PRUNE=process.env.DAG_CLEAN_PRUNE==='1';
const CONNECT=process.env.DAG_CONNECT!=='0';
const KIND_FIX={statement:'theorem'};
const STATUS_FIX={'PENDING-VERIFY':'CONDITIONAL'};
const REGIONS=new Set(['iuti-ii','iutiii','iutiv-abc','foundation','e-deep','mainline','routes','theta-etth','legacy-dag','iut-skeleton','iuti-ii-abc2']);
const fixId=(id)=>{ const p=id.split(':'); if(p.length>2 && REGIONS.has(p[1])) return p[0]+':'+p.slice(2).join(':'); return id; };
for(const n of dag.nodes){ if(KIND_FIX[n.kind]) n.kind=KIND_FIX[n.kind]; if(STATUS_FIX[n.status]) n.status=STATUS_FIX[n.status]; n.id=fixId(n.id); }
for(const e of dag.edges){ e.from=fixId(e.from); e.to=fixId(e.to); }
// drop missing files and declaration registrations pointing to missing files (validator hygiene)
for(const n of dag.nodes){
  if(Array.isArray(n.files)) n.files=n.files.filter(f=>existsSync(ROOT+'/'+f));
  if(n.declarations && typeof n.declarations==='object'){
    for(const p of Object.keys(n.declarations)){ if(!existsSync(ROOT+'/'+p)) delete n.declarations[p]; }
  }
}
const srcCache=new Map();
const readSrc=(p)=>{ if(srcCache.has(p)) return srcCache.get(p); let s=''; try{ s=readFileSync(p,'utf8'); }catch{} srcCache.set(p,s); return s; };
const shortName=(d)=>{ const i=d.lastIndexOf('.'); return i>=0?d.slice(i+1):d; };
for(const n of dag.nodes){ if(!n.declarations) continue; for(const [p,names] of Object.entries(n.declarations)){ if(!Array.isArray(names)) continue; const s=readSrc(p); n.declarations[p]=names.filter(d=>s.includes(shortName(d))); } }
const seen=new Set(); let edges=[]; for(const e of dag.edges){ const k=e.from+'|'+e.to+'|'+e.kind; if(seen.has(k)) continue; seen.add(k); edges.push(e); }
const ids=new Set(dag.nodes.map(n=>n.id));
let attached=0, fb=0, pruned=0; const candidates=[];
if(ATTACH){
  try{
    const imp=JSON.parse(readFileSync(ROOT+'/dag/generated/edges-imports.json','utf8')).edges;
    const fi=new Map(); for(const e of imp){ const f=e.from.replace(/^file:/,''); const t=e.to.replace(/^file:/,''); if(!fi.has(f))fi.set(f,[]); fi.get(f).push(t); }
    const fn=new Map(); for(const n of dag.nodes) for(const f of (n.files||[])){ if(!fn.has(f))fn.set(f,[]); fn.get(f).push(n.id); }
    const out=new Map(); for(const n of dag.nodes) out.set(n.id,[]); for(const e of edges){ if(out.has(e.from)) out.get(e.from).push(e); }
    const hasReal=(id)=>(out.get(id)||[]).some(e=>e.kind!=='hierarchy' && ids.has(e.to));
    for(const n of dag.nodes){ if(hasReal(n.id)) continue; let done=false; for(const f of (n.files||[])){ for(const t of (fi.get(f)||[])){ const tid=(fn.get(t)||[]).find(x=>x!==n.id && ids.has(x)); if(tid){ candidates.push({from:n.id,to:tid,source:'file-import',evidence:'observed_source',note:'SHEAF sec3: project import alone is NOT a dependency proof - candidate only'}); attached++; done=true; break; } } if(done) break; } }
  }catch{}
}
if(FALLBACK){
  const deg0=new Map(); for(const n of dag.nodes) deg0.set(n.id,0); for(const e of edges){ if(deg0.has(e.from))deg0.set(e.from,deg0.get(e.from)+1); if(deg0.has(e.to))deg0.set(e.to,deg0.get(e.to)+1); }
  const regionOf0=(id)=>{ const i=id.indexOf(':'); return i>0?id.slice(0,i):id; };
  const anchors=new Map(); for(const n of dag.nodes){ if((deg0.get(n.id)||0)>0 && !anchors.has(regionOf0(n.id))) anchors.set(regionOf0(n.id),n.id); }
  for(const n of dag.nodes){ if((deg0.get(n.id)||0)>0) continue; const a=anchors.get(regionOf0(n.id)); if(a&&a!==n.id){ edges.push({from:n.id,to:a,kind:'hierarchy',derived:true,evidence:'structural'}); fb++; deg0.set(n.id,1); } }
}
if(PRUNE){
  const stmtAdj=new Map(); for(const n of dag.nodes) stmtAdj.set(n.id,[]); for(const e of edges){ if(e.kind!=='statement') continue; if(!stmtAdj.has(e.from))stmtAdj.set(e.from,[]); if(!stmtAdj.has(e.to))stmtAdj.set(e.to,[]); stmtAdj.get(e.from).push(e); }
  const reach=(start,skip)=>{ const s=new Set(); const st=[start]; while(st.length){ const u=st.pop(); for(const e of (stmtAdj.get(u)||[])){ if(skip&&e.from===skip[0]&&e.to===skip[1]) continue; if(!s.has(e.to)){ s.add(e.to); st.push(e.to); } } } return s; };
  const kept=[]; for(const e of edges){ if(e.kind!=='statement'){ kept.push(e); continue; } const r=reach(e.from,[e.from,e.to]); if(r.has(e.to)) pruned++; else kept.push(e); } edges=kept;
}
let connectivityEdges=0, compsBefore=1;
if(CONNECT){
  const adjU=new Map(); for(const n of dag.nodes) adjU.set(n.id,[]);
  for(const e of edges){ if(!adjU.has(e.from))adjU.set(e.from,[]); if(!adjU.has(e.to))adjU.set(e.to,[]); adjU.get(e.from).push(e.to); adjU.get(e.to).push(e.from); }
  const comp=new Map(); compsBefore=0;
  for(const n of dag.nodes){ if(comp.has(n.id)) continue; compsBefore++; const st=[n.id]; comp.set(n.id,compsBefore); while(st.length){ const u=st.pop(); for(const v of (adjU.get(u)||[])){ if(!comp.has(v)){ comp.set(v,compsBefore); st.push(v); } } } }
  const compNodes=new Map(); for(const n of dag.nodes){ const c=comp.get(n.id); if(!compNodes.has(c))compNodes.set(c,[]); compNodes.get(c).push(n.id); }
  if(compsBefore>1){
    const mainComp=[...compNodes.entries()].sort((a,b)=>b[1].length-a[1].length)[0][0];
    const degA=new Map(); for(const n of dag.nodes)degA.set(n.id,0); for(const e of edges){ if(degA.has(e.from))degA.set(e.from,degA.get(e.from)+1); if(degA.has(e.to))degA.set(e.to,degA.get(e.to)+1); }
    const regionOf2=(id)=>{ const i=id.indexOf(':'); return i>0?id.slice(0,i):id; };
    const anchors2=new Map(); for(const id of compNodes.get(mainComp)){ const r=regionOf2(id); if(!anchors2.has(r)) anchors2.set(r,id); }
    for(const [c,ids2] of compNodes){ if(c===mainComp) continue; const rep=ids2.slice().sort((a,b)=>(degA.get(b)||0)-(degA.get(a)||0))[0]; const anchor=anchors2.get(regionOf2(rep))||compNodes.get(mainComp)[0]; edges.push({from:rep,to:anchor,kind:'hierarchy',derived:true,evidence:'structural'}); connectivityEdges++; }
  }
}
const deg=new Map(); for(const n of dag.nodes) deg.set(n.id,0); for(const e of edges){ if(deg.has(e.from))deg.set(e.from,deg.get(e.from)+1); if(deg.has(e.to))deg.set(e.to,deg.get(e.to)+1); }
const iso=dag.nodes.filter(n=>deg.get(n.id)===0).map(n=>n.id);
writeFileSync(ROOT+'/dag/declaration-dag.json', JSON.stringify({nodes:dag.nodes,edges,conflicts:[],merged_from:dag.merged_from||[]}));
writeFileSync(ROOT+'/dag/DAG-CANDIDATES.json', JSON.stringify({generated_at:new Date().toISOString(),policy:'SHEAF sec3: candidates are NOT dependencies (import/file-name/suffix/term are not proof)',candidates},null,2));
writeFileSync(ROOT+'/dag/DAG-CLEAN-REPORT.json', JSON.stringify({mode:{attach:ATTACH,fallback:FALLBACK,prune:PRUNE,connect:CONNECT},attached_import_edges:attached,fallback_hierarchy_attached:fb,pruned_transitive:pruned,connected_components_before:compsBefore,connectivity_edges:connectivityEdges,remaining_isolated:iso.length,isolated_ids:iso.slice(0,60),before_edges:dag.edges.length,after_edges:edges.length},null,2));
console.log(JSON.stringify({attached,fb,pruned,componentsBefore:compsBefore,connectivityEdges,isolated:iso.length,edges:edges.length}));