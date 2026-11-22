import { readFileSync, writeFileSync, existsSync, readdirSync, openSync, closeSync, unlinkSync, statSync } from 'node:fs';
import { join } from 'node:path';
const ROOT='D:/lean';
// A479 canonical mode: DAG is rebuilt from compiled .olean files (ground truth).
if(process.env.DAG_ALLOW_FRAGMENTS!=='1'){
  const { spawnSync } = await import('node:child_process');
  const r1=spawnSync(process.execPath,['--max-old-space-size=8192',join(ROOT,'tools','dag_rebuild_from_olean.mjs')],{cwd:ROOT,stdio:'inherit'});
  const r2=spawnSync(process.execPath,[join(ROOT,'tools','dag_clean2.mjs')],{cwd:ROOT,stdio:'inherit'});
  process.exit((r1.status||0)!==0?r1.status:(r2.status||0));
}
// advisory global lock: serialize concurrent merges from teammates/registry
const LOCK=join(ROOT,'dag','.merge.lock'); let lockFd=null;
for(let i=0;i<240;i++){ try{ lockFd=openSync(LOCK,'wx'); break; }catch{ try{ if(Date.now()-statSync(LOCK).mtimeMs>120000) unlinkSync(LOCK); }catch{} await new Promise(r=>setTimeout(r,500)); } }
const sources=[]; const main=join(ROOT,'dag','target-chain.json'); if(existsSync(main)) sources.push(main);
const coord=join(ROOT,'coord'); for(const f of readdirSync(coord)){ if(/^target-chain\..+\.json$/.test(f) && f!=='target-chain.TEMPLATE.json') sources.push(join(coord,f)); }
const nodes=new Map(); const edges=[]; const keys=new Set(); const conflicts=[]; const stats=[];
const allIdMap=new Map(); // raw global keys
for(const s of sources){ let j; try{ j=JSON.parse(readFileSync(s,'utf8')); }catch(e){ conflicts.push('parse '+s); continue; }
  const base=s.replaceAll('\\','/').split('/').pop(); const prefix=(base==='target-chain.json')?'':base.replace(/^target-chain\./,'').replace(/\.json$/,'')+':';
  const ns=j.nodes||[]; const es=j.edges||[]; stats.push({source:base,nodes:ns.length,edges:es.length,prefix}); const idmap=new Map();
  for(const n of ns){ const nid=prefix+n.id; idmap.set(n.id,nid); if(nodes.has(nid)){ conflicts.push('dup id '+nid); continue; } nodes.set(nid,{...n,id:nid}); allIdMap.set(n.id,nid); }
  for(const e of es){ let f=idmap.get(e.from)||(nodes.has(e.from)?e.from:null); let t=idmap.get(e.to)||(nodes.has(e.to)?e.to:null);
    if(!f||!t){ conflicts.push('edge unresolved '+base+': '+e.from+' -> '+e.to); continue; } const k=f+'|'+t+'|'+e.kind; if(!keys.has(k)){ keys.add(k); edges.push({from:f,to:t,kind:e.kind}); } }
}
writeFileSync(join(ROOT,'dag','declaration-dag.json'), JSON.stringify({generated_by:'tools/dag_merge3.mjs',merged_from:stats,node_count:nodes.size,edge_count:edges.length,conflicts,nodes:[...nodes.values()],edges},null,2));
console.log(JSON.stringify({sources:stats,nodes:nodes.size,edges:edges.length,conflicts:conflicts.length},null,2));
for(const c of conflicts.slice(0,10)) console.log('CONFLICT: '+c);
// auto-run connectivity/schema clean so every merge leaves a validated connected DAG
try { const { spawnSync } = await import('node:child_process'); spawnSync(process.execPath, [join(ROOT,'tools','dag_clean2.mjs')], { cwd: ROOT, stdio: 'ignore' }); } catch {}