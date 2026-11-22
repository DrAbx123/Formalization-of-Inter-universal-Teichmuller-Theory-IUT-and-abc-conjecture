import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const d=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const has=(id)=>d.nodes.some(n=>n.id===id);
const adds=[
 { id:'interface-radical-power-chain', title:'Cor312ToABCBridgeInterface => radical-power / log-form ABC chain',
   file:'tmp/sheaf/xif/paper/ShehddInterfaceRadicalPowerChainActual.lean',
   decls:['radicalPowerBound_of_interface','logBound_of_interface','heightBound_and_radicalPower_of_interface'],
   note:'PENDING-VERIFY (watchdog compile). New chain: cor312ToABCBridge_abcConjecture + abcConjecture_iff_rpow/abcLogConjecture (A476: real theorems only).',
   edgeCands:['T1-cor312-abc-bridge','mainline:abc-log-equivalence'] },
 { id:'frontier-elliptic-criteria-chain', title:'ABCFrontier => four elliptic height criteria chain',
   file:'tmp/sheaf/xif/paper/ShehddFrontierEllipticCriteriaChainActual.lean',
   decls:['freyJProductHeightCriterion_of_frontier','legendreJProductHeightCriterion_of_frontier','freyJDenominatorHeightCriterion_of_frontier','legendreJDenominatorHeightCriterion_of_frontier','abcFrontier_iff_freyJProductHeightCriterion'],
   note:'PENDING-VERIFY (watchdog compile). New chain: abcConjecture_of_frontier + four ABC<->criterion equivalences (A476: real theorems only).',
   edgeCands:['T3-abc-frontier','mainline:abc-freyj-criteria'] }
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
