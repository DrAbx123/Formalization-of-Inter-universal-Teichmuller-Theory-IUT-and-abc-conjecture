import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const adds=[
 { id:'abc-additive-form-consumer', title:'additive height-weight form consumer (constant extraction + uniform-valuation=>ABC)',
   file:'tmp/sheaf/xif/paper/ShehddABCAdditiveFormConsumerActual.lean',
   decls:['abcAdditive_exists_constant','abcConjecture_of_uniform_valuation_bound','abcConjecture_iff_additive_consumer','abcAdditiveRows','abcAdditiveRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Reuses ABCHeightArithmeticWeightComparison equivalences/API; uniform-valuation route is the documented vacuous retained implication.',
   edges:[['mainline:abc-height-weight-additive','statement'],['mainline:abc-log-equivalence','proof']] },
 { id:'cor312-tree-route-consumer', title:'Cor 3.12 tree route-certificate consumer (3 routes + q positivity)',
   file:'tmp/sheaf/xif/paper/ShehddCor312TreeRouteConsumerActual.lean',
   decls:['routeCertificate_conclusion','threeRoutes_conclusion','contract_q_pilot_positive','contract_conclusion','cor312TreeRouteRows','cor312TreeRouteRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Tree-only consumer (Contract/Routes/Comparison); contract construction from IUT source data remains the tree Obligation.',
   edges:[['iutiii:IUTIII.COR312.TARGET','statement'],['iutiv-abc:StepXI','proof']] }
];
for(const a of adds){
  if(j.nodes.some(n=>n.id===a.id)) continue;
  j.nodes.push({id:a.id,kind:'theorem',title:a.title,status:'CONDITIONAL',files:[a.file],declarations:{[a.file]:a.decls},note:a.note});
  for(const [to,kind] of a.edges) j.edges.push({from:a.id,to,kind,evidence:'observed_source'});
}
writeFileSync(p, JSON.stringify(j,null,2));
const extra=ROOT+'/dag/watchdog/extra-targets.txt';
let cur=readFileSync(extra,'utf8');
for(const a of adds){ if(!cur.includes(a.file)){ appendFileSync(extra, a.file+'\n'); cur+=a.file+'\n'; } }
console.log('my nodes='+j.nodes.length+' edges='+j.edges.length);
