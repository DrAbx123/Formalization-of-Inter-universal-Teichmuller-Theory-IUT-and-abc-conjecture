import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const d=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const has=(id)=>d.nodes.some(n=>n.id===id);
const adds=[
 { id:'qpilot-norm-inverse-chain', title:'q/j norm inverse and negated-log-volume exponential chain',
   file:'tmp/sheaf/xif/paper/ShehddQPilotNormInverseChainActual.lean',
   decls:['qNorm_eq_inv_jNorm','qNorm_eq_inv_prime','exp_neg_qPilotLogVolume','exp_neg_tateJInvariantLogVolume','log_qNorm_add_log_jNorm'],
   note:'PENDING-VERIFY (watchdog compile). New chain from TateQPilotJComparison/TateJInvariantNorm laws (A476: real theorems only).',
   edgeCands:['iut-pre-abc:QPilot','iut-skeleton:QPilot'] },
 { id:'interface-elliptic-criteria-chain', title:'Cor312ToABCBridgeInterface => four elliptic height criteria chain',
   file:'tmp/sheaf/xif/paper/ShehddInterfaceEllipticCriteriaChainActual.lean',
   decls:['freyJProductHeightCriterion_of_interface','legendreJProductHeightCriterion_of_interface','freyJDenominatorHeightCriterion_of_interface','legendreJDenominatorHeightCriterion_of_interface'],
   note:'PENDING-VERIFY (watchdog compile). New chain: interface ABCConjecture + four criterion equivalences (A476: real theorems only).',
   edgeCands:['T1-cor312-abc-bridge','mainline:abc-freyj-criteria'] }
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
