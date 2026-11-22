import { readFileSync, writeFileSync, existsSync, mkdirSync } from 'node:fs';
import { join } from 'node:path';
const ROOT='D:/lean'; const OUT=join(ROOT,'dag','watchdog'); mkdirSync(OUT,{recursive:true});
const dag=JSON.parse(readFileSync(join(ROOT,'dag','declaration-dag.json'),'utf8'));
let rt=null; try{ rt=JSON.parse(readFileSync(join(OUT,'runtime-status.json'),'utf8')); }catch{}
const rtMap=new Map(); if(rt) for(const n of rt.nodes) rtMap.set(n.id,n);
let b=[]; try{ b=JSON.parse(readFileSync(join(ROOT,'coord','DAG-BLOCKED.json'),'utf8')).blocked||[]; }catch{}
const blocked=new Set(b.map(x=>x.id)); const blockedReason=new Map(b.map(x=>[x.id,x.reason]));
const blockedFiles=new Set(); try{ const bj=JSON.parse(readFileSync(join(ROOT,'coord','DAG-BLOCKED.json'),'utf8')).blocked||[]; for(const e of bj){ const id=String(e.id||''); const m=id.match(/^sorries:n8-closure:(.+)$/); if(m) blockedFiles.add('tmp/sheaf/n8/closure/'+m[1]+'.lean'); if(e.file) blockedFiles.add(e.file); } }catch{}
const deps=new Map(), dependents=new Map(); for(const n of dag.nodes){ deps.set(n.id,[]); dependents.set(n.id,[]); }
for(const e of dag.edges){ if(!deps.has(e.from)) continue; deps.get(e.from).push(e.to); if(dependents.has(e.to)) dependents.get(e.to).push(e.from); }
const proved=id=>{ const n=dag.nodes.find(x=>x.id===id); return n && ['PROVED','BOTTOM'].includes(n.status); };
const actionableStates=new Set(['NAMED','GAP','CONDITIONAL','DEF']);
const nodes=dag.nodes.filter(n=>actionableStates.has(n.status) && !blocked.has(n.id) && !(n.files||[]).some(f=>blockedFiles.has(f)) && !n.id.startsWith('legacy-dag:') && n.kind!=='route_mention' && n.kind!=='paper_label');
const scored=nodes.map(n=>{ const ds=deps.get(n.id)||[]; const unproved=ds.filter(d=>!proved(d)); const r=rtMap.get(n.id); const evidence=r?{mismatch:r.mismatch,files:r.files,all_fresh:r.all_fresh,exits_ok:r.exits_ok}:null; return {id:n.id,kind:n.kind,status:n.status,title:(n.title||'').slice(0,100),files:(n.files||[]).slice(0,3),deps:ds.length,unproved_deps:unproved.length,evidence}; });
scored.sort((a,b)=>(a.unproved_deps-b.unproved_deps)||(a.kind==='named_input'?1:0)-(b.kind==='named_input'?1:0));
writeFileSync(join(OUT,'next.json'), JSON.stringify({generated_at:new Date().toISOString(), actionable:scored.length, blocked:blocked.size, top:scored.slice(0,80)},null,2));
const lines=['# DAG NEXT — actionable nodes (no blocked/refuted/detoured)','','generated: '+new Date().toISOString(),'','blocked/refuted/detoured excluded: '+blocked.size,'','| # | id | kind | status | unproved deps | files |','|---|---|---|---|---|---|'];
scored.slice(0,60).forEach((n,i)=>lines.push('| '+(i+1)+' | '+n.id+' | '+n.kind+' | '+n.status+' | '+n.unproved_deps+' | '+((n.files||[]).join('<br>'))+' |'));
writeFileSync(join(ROOT,'coord','DAG-NEXT.md'), lines.join('\n'));
console.log(JSON.stringify({actionable:scored.length, blocked:blocked.size, ready:scored.filter(n=>n.unproved_deps===0).length},null,2));
scored.slice(0,25).forEach((n,i)=>console.log((i+1)+'. ['+n.status+'] '+n.id+'  ('+(n.files[0]||'')+')'));