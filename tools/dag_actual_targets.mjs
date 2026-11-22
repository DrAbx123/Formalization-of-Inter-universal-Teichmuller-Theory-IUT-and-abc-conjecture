import { readFileSync, writeFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const dag=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.fragments-backup.json','utf8'));
let blocked=[]; try{ blocked=JSON.parse(readFileSync(ROOT+'/coord/DAG-BLOCKED.json','utf8')).blocked||[]; }catch{}
const blockedIds=new Set(blocked.map(x=>x.id));
const actionableStates=new Set(['CONDITIONAL','GAP','NAMED','DEF']);
const kindOk=new Set(['theorem','target','bridge','named_input','def','bottom','conditional']);
const rows=dag.nodes.filter(n=>actionableStates.has(n.status)&&kindOk.has(n.kind)&&!blockedIds.has(n.id));
const byPrefix={}; for(const n of rows){ const p=n.id.split(':')[0]; (byPrefix[p]=byPrefix[p]||[]).push(n); }
const groups=Object.entries(byPrefix).sort((a,b)=>b[1].length-a[1].length);
const md=['# ACTUAL TARGETS (from archived semantic DAG, after A479 olean-DAG switch)','','generated: '+new Date().toISOString(),'','total actionable semantic nodes: '+rows.length,'','## by region','','| region | nodes | sample ids |','|---|---|---|'];
for(const [p,list] of groups) md.push('| '+p+' | '+list.length+' | '+list.slice(0,3).map(n=>n.id).join('<br>')+' |');
md.push('','## full list','','| id | kind | status | files |','|---|---|---|---|');
for(const n of rows) md.push('| '+n.id+' | '+n.kind+' | '+n.status+' | '+((n.files||[]).slice(0,2).join('<br>'))+' |');
writeFileSync(ROOT+'/coord/ACTUAL-TARGETS.md', md.join('\n'));
// json compact for tooling
writeFileSync(ROOT+'/coord/ACTUAL-TARGETS.json', JSON.stringify({generated_at:new Date().toISOString(), total:rows.length, by_region:Object.fromEntries(groups.map(([p,l])=>[p,l.length])), targets:rows.map(n=>({id:n.id,kind:n.kind,status:n.status,files:(n.files||[]).slice(0,3),title:(n.title||'').slice(0,120)}))},null,2));
console.log(JSON.stringify({total:rows.length, regions:groups.map(([p,l])=>p+':'+l.length)},null,2).slice(0,1200));