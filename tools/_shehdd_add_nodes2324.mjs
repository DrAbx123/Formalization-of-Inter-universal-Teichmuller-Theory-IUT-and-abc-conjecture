import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const d=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const has=(id)=>d.nodes.some(n=>n.id===id);
const adds=[
 { id:'frey-tate-candidate-consumer', title:'Frey/Tate q-parameter candidate analytic consumer (q=j^-1, arithmetic certificate)',
   file:'tmp/sheaf/xif/paper/ShehddFreyTateQCandidateConsumerActual.lean',
   decls:['freyTate_candidate_summary','freyTate_candidate_norm_summary','freyTate_candidate_arithmeticCertificate','freyTateCandidateRows','freyTateCandidateRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Reuses FreyTateAnalyticInput/ParameterComparison (q=j^-1, ||q||<1, <=1/9, arithmetic certificate).',
   edges:[['mainline:frey-odd-reduction','statement'],['T3-abc-frontier','proof']] },
 { id:'abc-invariant-coprimality-consumer', title:'ABC invariant coprimality + cancellation bound consumer',
   file:'tmp/sheaf/xif/paper/ShehddABCInvariantCoprimalityConsumerActual.lean',
   decls:['abcInvariant_coprime_summary','abcInvariant_cancellation_summary','abcInvariant_cancellation_eq_gcd','abcInvariantCoprimalityRows','abcInvariantCoprimalityRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Reuses ABCInvariantCoprimality pairwise/product coprimality and cancellation bounds.',
   edges:[['mainline:abc-invariant-coprimality','statement'],['T0-abc-target','proof']] }
];
for(const a of adds){
  if(j.nodes.some(n=>n.id===a.id)) continue;
  const edges=a.edges.filter(([to])=>has(to));
  const dropped=a.edges.filter(([to])=>!has(to)).map(([to])=>to);
  j.nodes.push({id:a.id,kind:'theorem',title:a.title,status:'CONDITIONAL',files:[a.file],declarations:{[a.file]:a.decls},note:a.note+(dropped.length?(' Dropped unresolved edge targets: '+dropped.join(',')):'')});
  for(const [to,kind] of edges) j.edges.push({from:a.id,to,kind,evidence:'observed_source'});
}
writeFileSync(p, JSON.stringify(j,null,2));
const extra=ROOT+'/dag/watchdog/extra-targets.txt';
let cur=readFileSync(extra,'utf8');
for(const a of adds){ if(!cur.includes(a.file)){ appendFileSync(extra, a.file+'\n'); cur+=a.file+'\n'; } }
console.log('my nodes='+j.nodes.length+' edges='+j.edges.length);
