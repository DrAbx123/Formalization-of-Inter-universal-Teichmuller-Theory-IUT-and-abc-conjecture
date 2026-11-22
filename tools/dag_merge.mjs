import { readFileSync, writeFileSync, existsSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
const ROOT='D:/lean';
const sources=[];
const main=join(ROOT,'dag','target-chain.json');
if(existsSync(main)) sources.push(main);
const coord=join(ROOT,'coord');
for(const f of readdirSync(coord)){ if(/^target-chain\..+\.json$/.test(f)) sources.push(join(coord,f)); }
const nodes=new Map(); const edges=[]; const edgeKeys=new Set(); const conflicts=[]; const sourceStats=[];
for(const s of sources){ let j; try{ j=JSON.parse(readFileSync(s,'utf8')); }catch(e){ conflicts.push('cannot parse '+s+': '+e.message); continue; } const ns=j.nodes||[]; const es=j.edges||[]; sourceStats.push({source:s.replaceAll('\\','/').replace(ROOT+'/',''), nodes:ns.length, edges:es.length});
  for(const n of ns){ if(nodes.has(n.id)){ const prev=nodes.get(n.id); const same=JSON.stringify(prev)===JSON.stringify(n); if(!same) conflicts.push('node id conflict: '+n.id+' ('+prev.files+' vs '+n.files+')'); continue; } nodes.set(n.id,n); }
  for(const e of es){ const k=e.from+'|'+e.to+'|'+e.kind; if(!edgeKeys.has(k)){ edgeKeys.add(k); edges.push(e); } } }
const out={ generated_by:'tools/dag_merge.mjs', merged_from:sourceStats, node_count:nodes.size, edge_count:edges.length, conflicts, nodes:[...nodes.values()], edges };
writeFileSync(join(ROOT,'dag','declaration-dag.json'), JSON.stringify(out,null,2));
console.log(JSON.stringify({sources:sourceStats, nodes:nodes.size, edges:edges.length, conflicts:conflicts.length}, null, 2));
for(const c of conflicts.slice(0,10)) console.log('CONFLICT: '+c);