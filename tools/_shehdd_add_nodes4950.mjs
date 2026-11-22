import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const d=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const has=(id)=>d.nodes.some(n=>n.id===id);
const adds=[
 { id:'punctured-curve-consumer', title:'punctured elliptic curve map/baseChange consumer',
   file:'tmp/sheaf/xif/paper/ShehddPuncturedCurveConsumerActual.lean',
   decls:['punctured_curve_jInvariant_consumer','punctured_curve_map_consumer','punctured_curve_baseChange_consumer','puncturedCurveRows','puncturedCurveRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Reuses PuncturedEllipticCurve map/baseChange laws.',
   edgeCands:['mainline:frey-odd-reduction','iut-pre-abc:QPilot'] },
 { id:'tate-delta-estimates-consumer', title:'Tate discriminant decomposition / constant norm estimates consumer',
   file:'tmp/sheaf/xif/paper/ShehddTateDeltaEstimatesConsumerActual.lean',
   decls:['deltaValue_decomposition_consumer','deltaValue_series_consumer','deltaValue_constant_bounds_consumer','tateDeltaRows','tateDeltaRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Reuses TateCurveDiscriminantEstimates decomposition/bounds.',
   edgeCands:['iut-pre-abc:QPilot','iut-skeleton:QPilot'] }
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
