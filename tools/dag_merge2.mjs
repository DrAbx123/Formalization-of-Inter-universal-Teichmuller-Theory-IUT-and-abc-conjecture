import { readFileSync, writeFileSync, existsSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
const ROOT='D:/lean';
const sources=[];
const main=join(ROOT,'dag','target-chain.json');
if(existsSync(main)) sources.push(main);
const coord=join(ROOT,'coord');
for(const f of readdirSync(coord)){ if(/^target-chain\..+\.json$/.test(f) && f !== 'target-chain.TEMPLATE.json') sources.push(join(coord,f)); }
const nodes=new Map(); const edges=[]; const edgeKeys=new Set(); const conflicts=[]; const sourceStats=[];
for(const s of sources){
  let j; try{ j=JSON.parse(readFileSync(s,'utf8')); }catch(e){ conflicts.push('parse '+s); continue; }
  const base=s.replaceAll('\\','/').split('/').pop();
  const prefix=(base==='target-chain.json') ? '' : base.replace(/^target-chain\./,'').replace(/\.json$/,'') + ':';
  const ns=j.nodes||[]; const es=j.edges||[];
  sourceStats.push({ source:s.replaceAll('\\','/').replace(ROOT+'/',''), nodes:ns.length, edges:es.length, prefix });
  const idmap=new Map();
  for(const n of ns){ const nid=prefix+n.id; idmap.set(n.id,nid); if(nodes.has(nid)){ conflicts.push('node id conflict: '+nid); continue; } nodes.set(nid,{...n,id:nid}); }
  for(const e of es){ const f=idmap.get(e.from); const t=idmap.get(e.to); if(!f||!t){ conflicts.push('fragment edge outside nodes: '+s+' '+e.from+'->'+e.to); continue; } const k=f+'|'+t+'|'+e.kind; if(!edgeKeys.has(k)){ edgeKeys.add(k); edges.push({from:f,to:t,kind:e.kind}); } }
}
const out={ generated_by:'tools/dag_merge2.mjs', merged_from:sourceStats, node_count:nodes.size, edge_count:edges.length, conflicts, nodes:[...nodes.values()], edges };
writeFileSync(join(ROOT,'dag','declaration-dag.json'), JSON.stringify(out,null,2));
console.log(JSON.stringify({sources:sourceStats, nodes:nodes.size, edges:edges.length, conflicts:conflicts.length},null,2));
for(const c of conflicts.slice(0,10)) console.log('CONFLICT: '+c);