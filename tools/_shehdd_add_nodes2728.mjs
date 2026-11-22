import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const d=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const has=(id)=>d.nodes.some(n=>n.id===id);
const cands=[['mainline:abc-frontier-heightweight-refutation','proof'],['mainline:abc-frontier','proof'],['T0-abc-target','proof']];
const adds=[
 { id:'logshell-identification-consumer', title:'log-shell invariant image identification consumer (bridge card consequences)',
   file:'tmp/sheaf/xif/paper/ShehddLogShellIdentificationConsumerActual.lean',
   decls:['logShellIdentification_consumer','logShellIdentification_upperSemi','logShellIdentificationRows','logShellIdentificationRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Reuses SourceLogShellAbsTopIIIBridge bridge-card equivalences/consequences; source arithmetic fact remains the named card.',
   edges:[['iutiii:IUTIII.STEPXI.LOGSHELL_MUN','statement'],['e-deep:E1.logShellBridge','proof']] },
 { id:'frontier-reduction-consumer', title:'frontier reduction implications with refuted premises (vacuous routes)',
   file:'tmp/sheaf/xif/paper/ShehddFrontierReductionConsumerActual.lean',
   decls:['frontier_reductions_with_empty_premises','frontier_reduction_routes_vacuous','frontierReductionRows','frontierReductionRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Connects ABCFrontierReductions implications with ABCFrontierHeightWeightRefutation empty-premise results.',
   edges:[['T3-abc-frontier','statement']] }
];
for(const a of adds){
  if(j.nodes.some(n=>n.id===a.id)) continue;
  let edges=a.edges.filter(([to])=>has(to));
  if(a.id==='frontier-reduction-consumer'){ const extra=cands.find(([to])=>has(to)); if(extra) edges=edges.concat([extra]); }
  const dropped=a.edges.filter(([to])=>!has(to)).map(([to])=>to);
  j.nodes.push({id:a.id,kind:'theorem',title:a.title,status:'CONDITIONAL',files:[a.file],declarations:{[a.file]:a.decls},note:a.note+(dropped.length?(' Dropped unresolved edge targets: '+dropped.join(',')):'')});
  for(const [to,kind] of edges) j.edges.push({from:a.id,to,kind,evidence:'observed_source'});
}
writeFileSync(p, JSON.stringify(j,null,2));
const extra=ROOT+'/dag/watchdog/extra-targets.txt';
let cur=readFileSync(extra,'utf8');
for(const a of adds){ if(!cur.includes(a.file)){ appendFileSync(extra, a.file+'\n'); cur+=a.file+'\n'; } }
console.log('my nodes='+j.nodes.length+' edges='+j.edges.length);
