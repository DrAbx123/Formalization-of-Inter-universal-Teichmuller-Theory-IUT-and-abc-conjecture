import { readFileSync, writeFileSync, existsSync, statSync, mkdirSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
const ROOT='D:/lean'; const OUT=join(ROOT,'dag','watchdog'); mkdirSync(OUT,{recursive:true});
const GEN=join(ROOT,'dag','generated');
const CACHE=join(OUT,'graph-cache.json');
const needCache=!existsSync(CACHE)||statSync(CACHE).mtimeMs < Math.max(statSync(join(GEN,'nodes-files.json')).mtimeMs, statSync(join(GEN,'edges-imports.json')).mtimeMs);
let cache;
if(needCache){
  const nodes=JSON.parse(readFileSync(join(GEN,'nodes-files.json'),'utf8')).nodes;
  const edges=JSON.parse(readFileSync(join(GEN,'edges-imports.json'),'utf8')).edges;
  const imports={}; const known=[];
  for(const n of nodes){ known.push(n.path); imports[n.path]=[]; }
  for(const e of edges){ const f=e.from.replace(/^file:/,''); const t=e.to.replace(/^file:/,''); if(imports[f]) imports[f].push(t); }
  cache={imports,known}; writeFileSync(CACHE,JSON.stringify(cache));
} else { cache=JSON.parse(readFileSync(CACHE,'utf8')); }
const imports=new Map(); const known=new Set();
for(const p of cache.known){ known.add(p); imports.set(p,cache.imports[p]||[]); }
const files=new Set();
const EXTRA_ONLY=(process.env.DAG_SEEDS||"")==="extra";
const addFiles=(j)=>{ if(EXTRA_ONLY) return; for(const n of (j.nodes||[])) for(const f of (n.files||[])) if(typeof f==='string' && f.endsWith('.lean')) files.add(f); };
const dpath=join(ROOT,'dag','declaration-dag.json'); if(existsSync(dpath)) addFiles(JSON.parse(readFileSync(dpath,'utf8')));
const tpath=join(ROOT,'dag','target-chain.json'); if(existsSync(tpath)) addFiles(JSON.parse(readFileSync(tpath,'utf8')));
for(const f of readdirSync(join(ROOT,'coord'))){ if(/^target-chain\..+\.json$/.test(f) && f!=='target-chain.TEMPLATE.json'){ try{ addFiles(JSON.parse(readFileSync(join(ROOT,'coord',f),'utf8'))); }catch{} } }
const extra=[];
try{ for(const line of readFileSync(join(OUT,'extra-targets.txt'),'utf8').split(/\r?\n/)){ const p=line.trim().replaceAll('\\','/'); if(p.endsWith('.lean')&&existsSync(join(ROOT,p))) extra.push(p); } }catch{}
for(const p of extra) files.add(p);
const closure=new Set(); const stack=[...files]; while(stack.length){ const p=stack.pop(); if(closure.has(p)) continue; closure.add(p); for(const q of (imports.get(p)||[])) if(!closure.has(q)) stack.push(q); }
const portedPrefix=ROOT+'/tmp/external/ported/';
const oleanCands=(p)=>{ const cands=[]; const rel=p.replace(/\.lean$/,'');
  if(p.startsWith(portedPrefix)){ const rest=p.slice(portedPrefix.length); const pkg=rest.split('/')[0]; const pkgRoot=portedPrefix+pkg+'/'; const modRel=p.slice(pkgRoot.length).replace(/\.lean$/,''); cands.push(join(ROOT,'.lake','build','lib','lean',modRel+'.olean')); }
  cands.push(join(ROOT,'.lake','build','lib','lean',rel+'.olean')); return cands; };
const statePath=join(OUT,'state.json'); let state={}; try{ state=JSON.parse(readFileSync(statePath,'utf8')); }catch{}
const now=Date.now(); const dirty=[]; const missing=[];
for(const p of closure){ const abs=join(ROOT,p); if(!existsSync(abs)){ missing.push(p); continue; } const srcM=statSync(abs).mtimeMs;
  let olean=null; for(const c of oleanCands(p)) if(existsSync(c)){ const om=statSync(c).mtimeMs; if(olean===null||om>olean) olean=om; }
  const stale=olean===null||olean<srcM; const e=state[p]; const retry=e&&e.failed_exit!==undefined&&e.failed_mtime===srcM&&(now-(e.failed_at||0)<600000);
  if(stale&&!retry&&!/Mzk1(ABCTwoEstimatesHeightLemmasSha|AcceptanceFinalChecks)Actual/.test(p)) dirty.push(p); }
const order=[]; const mark=new Map(); const visit=(p)=>{ const m=mark.get(p); if(m) return; mark.set(p,1); for(const q of (imports.get(p)||[])) if(closure.has(q)) visit(q); order.push(p); };
for(const p of closure) visit(p); const oi=new Map(); order.forEach((p,i)=>oi.set(p,i));
const STAT=statSync; const isProbe=(p)=>/(^|\/)_[^/]*\.lean$/.test(p); const ageOf=(p)=>{ try{ return Date.now()-STAT(join(ROOT,p)).mtimeMs; }catch{ return 1e12; } };
const prio=new Set(); try{ for(const line of readFileSync(join(OUT,'priority-files.txt'),'utf8').split(/\r?\n/)){ const p=line.trim().replaceAll('\\','/'); if(p) prio.add(p); } }catch{}
const tierOf=(p)=>{ if(prio.has(p)) return -1; if(isProbe(p)) return 2; return ageOf(p)<900000?0:1; };
const sorted=dirty.sort((a,b)=>{ const ta=tierOf(a), tb=tierOf(b); if(ta!==tb) return ta-tb; return (oi.get(a)??1e9)-(oi.get(b)??1e9); });
writeFileSync(join(OUT,'plan.json'), JSON.stringify({generated_at:new Date().toISOString(), targets:files.size, extra_targets:extra.length, closure:closure.size, missing_files:missing, dirty_count:sorted.length, dirty:sorted},null,2));
writeFileSync(join(OUT,'order.json'), JSON.stringify({order,closure:[...closure]},null,2));
console.log(JSON.stringify({targets:files.size, extra:extra.length, closure:closure.size, dirty:sorted.length, missing:missing.length},null,2));