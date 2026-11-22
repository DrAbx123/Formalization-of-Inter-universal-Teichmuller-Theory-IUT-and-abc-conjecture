import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const d=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const has=(id)=>d.nodes.some(n=>n.id===id);
const adds=[
 { id:'radical-laws-consumer', title:'natRadical arithmetic laws consumer (multiplicativity/power/divisibility)',
   file:'tmp/sheaf/xif/paper/ShehddRadicalLawsConsumerActual.lean',
   decls:['natRadical_basic_consumer','natRadical_mul_consumer','natRadical_pow_dvd_consumer','radicalLawsRows','radicalLawsRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Reuses Foundations/Arithmetic/Radical laws.',
   edgeCands:['T0-abc-target','mainline:abc-invariant-radical-bridge'] },
 { id:'badprime-tate-input-consumer', title:'odd bad-prime Frey/Tate analytic input consumer',
   file:'tmp/sheaf/xif/paper/ShehddBadPrimeTateInputConsumerActual.lean',
   decls:['frey_badprime_candidate_ne_zero_consumer','frey_badprime_candidate_norm_lt_one_consumer','frey_badprime_candidate_ne_one_consumer','exists_tate_input_consumer','badPrimeTateRows','badPrimeTateRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Reuses ABCModelHeightComparison bad-prime candidate facts; no uniformization claim.',
   edgeCands:['mainline:frey-odd-reduction','T3-abc-frontier'] }
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
