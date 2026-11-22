import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const d=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const has=(id)=>d.nodes.some(n=>n.id===id);
const adds=[
 { id:'tate-canonical-coefficients-consumer', title:'Tate canonical equation coefficients/invariants consumer (q-series model)',
   file:'tmp/sheaf/xif/paper/ShehddTateCanonicalCoefficientsConsumerActual.lean',
   decls:['tateCanonical_consumer','tateCanonical_relations_consumer','tateCanonicalRows','tateCanonicalRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Reuses TateCurveArithmetic canonical coefficients/relations.',
   edgeCands:['iut-pre-abc:QPilot','iut-skeleton:QPilot'] },
 { id:'frey-weierstrass-consumer', title:'Frey Weierstrass model invariant/scaling/ellipticity consumer',
   file:'tmp/sheaf/xif/paper/ShehddFreyWeierstrassConsumerActual.lean',
   decls:['freyWeierstrass_invariants_consumer','freyWeierstrass_scaling_consumer','freyWeierstrass_isElliptic_consumer','freyWeierstrassRows','freyWeierstrassRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Reuses FreyWeierstrassCurve invariant/scaling/ellipticity laws.',
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
