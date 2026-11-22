import { readFileSync, writeFileSync, existsSync, statSync, unlinkSync, openSync, closeSync } from 'node:fs';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';
const ROOT='D:/lean'; const DAG=join(ROOT,'dag'); const LOCK=join(DAG,'.registry.lock');
let fd=null; try{ fd=openSync(LOCK,'wx'); }catch{ console.log('locked, skip'); process.exit(0); }
const run=(s)=>{ const r=spawnSync(process.execPath,[join(ROOT,'tools',s)],{cwd:ROOT,encoding:'utf8',maxBuffer:1024*1024*64}); return {code:r.status,out:(r.stdout||'').slice(-2000),err:(r.stderr||'').slice(-1000)}; };
const t0=Date.now();
const merge=run('dag_merge3.mjs');
const exp=run('dag_export_nodes.mjs');
const d=JSON.parse(readFileSync(join(DAG,'declaration-dag.json'),'utf8'));
const g=new Map(); for(const n of d.nodes) g.set(n.id,[]); for(const e of d.edges){ if(g.has(e.from))g.get(e.from).push(e.to); if(g.has(e.to))g.get(e.to).push(e.from); }
let seen=new Set(), comps=0; for(const n of d.nodes){ if(seen.has(n.id)) continue; comps++; const st=[n.id]; seen.add(n.id); while(st.length){ const u=st.pop(); for(const v of (g.get(u)||[])){ if(!seen.has(v)){ seen.add(v); st.push(v); } } } }
const kinds={}; for(const e of d.edges) kinds[e.kind]=(kinds[e.kind]||0)+1;
const status={}; for(const n of d.nodes) status[n.status]=(status[n.status]||0)+1;
const report={generated_at:new Date().toISOString(), ms:Date.now()-t0, nodes:d.nodes.length, edges:d.edges.length, conflicts:(d.conflicts||[]).length, components:comps, edge_kinds:kinds, node_status:status, merge_ok:merge.code===0, export_ok:exp.code===0};
writeFileSync(join(DAG,'DAG-STATUS.md'), ['# DAG status (auto registry tick)','','generated: '+report.generated_at,'','| metric | value |','|---|---|','| nodes | '+report.nodes+' |','| edges | '+report.edges+' |','| conflicts | '+report.conflicts+' |','| components | '+report.components+' |','| edge kinds | '+JSON.stringify(kinds)+' |','| node status | '+JSON.stringify(status)+' |','| tick ms | '+report.ms+' |',''].join('\n'));
writeFileSync(join(DAG,'DAG-STATUS.json'), JSON.stringify(report,null,2));
try{ closeSync(fd); unlinkSync(LOCK); }catch{}
console.log(JSON.stringify(report));