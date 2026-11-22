import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const d=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const has=(id)=>d.nodes.some(n=>n.id===id);
const adds=[
 { id:'matrix-logdet-laws-consumer', title:'matrix log-det law bundle (mul / smul / Kronecker / pow)',
   file:'tmp/sheaf/xif/paper/ShehddMatrixLogDetLawsConsumerActual.lean',
   decls:['matrixLogDet_laws_consumer','matrixLogDetRows','matrixLogDetRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Reuses HullDeterminantLogVolumeReduction matrix log-det laws for (Ob3-2)/(Ob3-3) bookkeeping.',
   edges:[['iutiii:IUTIII.HULL.DET_LOG_VOLUME','statement'],['e-deep:E2.detScalingLaws','proof']] },
 { id:'elliptic-height-criteria-consumer', title:'ABC elliptic height criteria consumer (4 criteria equivalences)',
   file:'tmp/sheaf/xif/paper/ShehddEllipticHeightCriteriaConsumerActual.lean',
   decls:['elliptic_height_criteria_equivalent','freyProduct_iff_legendreDenominator','ellipticHeightCriteriaRows','ellipticHeightCriteriaRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Reuses ABCEllipticHeightCriterion proved equivalences for Frey/Legendre j product/denominator criteria.',
   edges:[['mainline:abc-freyj-criteria','statement'],['T0-abc-target','proof']] }
];
for(const a of adds){
  if(j.nodes.some(n=>n.id===a.id)) continue;
  let edges=a.edges.filter(([to])=>has(to));
  for(const [to,kind] of a.edges){ if(!has(to)&&!edges.some(([x])=>x===to)){ if(has('T3-abc-frontier')) edges.push(['T3-abc-frontier',kind]); } }
  const dropped=a.edges.filter(([to])=>!has(to)&&!edges.some(([x])=>x===to)).map(([to])=>to);
  j.nodes.push({id:a.id,kind:'theorem',title:a.title,status:'CONDITIONAL',files:[a.file],declarations:{[a.file]:a.decls},note:a.note+(dropped.length?(' Dropped unresolved edge targets: '+dropped.join(',')):'')});
  for(const [to,kind] of edges) j.edges.push({from:a.id,to,kind,evidence:'observed_source'});
}
writeFileSync(p, JSON.stringify(j,null,2));
const extra=ROOT+'/dag/watchdog/extra-targets.txt';
let cur=readFileSync(extra,'utf8');
for(const a of adds){ if(!cur.includes(a.file)){ appendFileSync(extra, a.file+'\n'); cur+=a.file+'\n'; } }
console.log('my nodes='+j.nodes.length+' edges='+j.edges.length);
