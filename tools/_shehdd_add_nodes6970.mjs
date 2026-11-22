import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const d=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const has=(id)=>d.nodes.some(n=>n.id===id);
const adds=[
 { id:'section-map-chain', title:'place-partition label iff + section-map bijectivity chain',
   file:'tmp/sheaf/xif/paper/ShehddSectionMapChainActual.lean',
   decls:['placePartition_label_iff_chain','sectionMap_bijective_chain','sectionRightInverse_bijective_chain'],
   note:'PENDING-VERIFY (watchdog compile). New chain from SourceDefinition31Boundary laws (A476: real theorems only).',
   edgeCands:['iutiii:IUTIII.THM311.OUTPUT_ALGORITHM','iutiii:IUTIII.STEPXI.LOGSHELL_MUN'] },
 { id:'integral-units-chain', title:'integral units norm-one/integer-ring/compactness chain',
   file:'tmp/sheaf/xif/paper/ShehddIntegralUnitsChainActual.lean',
   decls:['unit_norm_and_integer_chain','unitOfNormOne_chain','units_topology_chain'],
   note:'PENDING-VERIFY (watchdog compile). New chain from IntegralUnits laws (A476: real theorems only).',
   edgeCands:['e-deep:E1.logShellBridge','iutiii:IUTIII.STEPXI.LOGSHELL_MUN'] }
];
for(const a of adds){
  if(j.nodes.some(n=>n.id===a.id)) continue;
  const edges=[];
  for(const cand of a.edgeCands){ if(has(cand)&&!edges.some(([t])=>t===cand)) edges.push([cand, edges.length===0?'statement':'proof']); }
  j.nodes.push({id:a.id,kind:'theorem',title:a.title,status:'CONDITIONAL',files:[a.file],declarations:{[a.file]:a.decls},note:a.note});
  for(const [to,kind] of edges) j.edges.push({from:a.id,to,kind,evidence:'observed_source'});
}
writeFileSync(p, JSON.stringify(j,null,2));
const extra=ROOT+'/dag/watchdog/extra-targets.txt';
let cur=readFileSync(extra,'utf8');
for(const a of adds){ if(!cur.includes(a.file)){ appendFileSync(extra, a.file+'\n'); cur+=a.file+'\n'; } }
console.log('my nodes='+j.nodes.length+' edges='+j.edges.length);
