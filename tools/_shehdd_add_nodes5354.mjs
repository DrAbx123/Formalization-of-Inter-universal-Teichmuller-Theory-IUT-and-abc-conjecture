import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const d=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const has=(id)=>d.nodes.some(n=>n.id===id);
const adds=[
 { id:'qpilot-exp-chain', title:'q-pilot/j-invariant log-volume exponential chain (exp volumes, additive law)',
   file:'tmp/sheaf/xif/paper/ShehddQPilotExpChainActual.lean',
   decls:['qPilotLogVolume_exp_eq_prime','tateJInvariantLogVolume_exp_eq_norm','qPilotLogVolume_add_tateJInvariantLogVolume','exp_add_eq_prime_mul_norm','one_lt_exp_qPilotLogVolume'],
   note:'PENDING-VERIFY (watchdog compile). New chain consequences of TateQPilotJComparison log-volume laws (A476: real theorems only, no bookkeeping rows).',
   edgeCands:['iut-pre-abc:QPilot','iut-skeleton:QPilot'] },
 { id:'frontier-forms-chain', title:'ABCFrontier <-> log/additive ABC forms chain',
   file:'tmp/sheaf/xif/paper/ShehddFrontierFormsChainActual.lean',
   decls:['abcLogConjecture_of_frontier','abcHeightWeightAdditive_of_frontier','abcFrontier_iff_abcLogConjecture','abcFrontier_iff_additive'],
   note:'PENDING-VERIFY (watchdog compile). New chain composition of abcFrontier_iff_abcConjecture with the proved ABC form equivalences (A476: real theorems only).',
   edgeCands:['T3-abc-frontier','mainline:abc-log-equivalence'] }
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
