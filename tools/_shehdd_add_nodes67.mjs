import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const adds=[
 { id:'ind3-closure-laws', kind:'theorem',
   title:'(Ind3) upper-semi possible-image closure laws (isLowerClosed <-> closure = self)',
   file:'tmp/sheaf/xif/paper/ShehddInd3ClosureLawsActual.lean',
   decls:['isLowerClosed_iff_lowerClosure_eq_self','lowerClosure_le_iff_carrier_subset','lowerClosure_eq_self_of_isLowerClosed','ind3ClosureRows','ind3ClosureRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Adds order-theoretic closure laws to Ind3Reduction possible images; analytic (Ind3) log-Kummer carriers remain NAMED (Ind3.lean audit note).',
   edges:[['iutiii:IUTIII.IND3','statement'],['iut-skeleton:Ind3','proof']] },
 { id:'packet-log-volume-laws', kind:'theorem',
   title:'packet log-volume tensor / rescale / tensor-power laws (discharge of determinant bookkeeping composites)',
   file:'tmp/sheaf/xif/paper/ShehddPacketLogVolumeLawsActual.lean',
   decls:['packetLogVolume_tensor','packetLogVolume_rescale','packetLogVolume_tensorPower_matrix','packetLogVolumeRows','packetLogVolumeRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Composes matrixLogDet kronecker/smul/pow laws with packetDiagonalMatrix laws; (Ob3-2)/(Ob3-3) determinant bookkeeping consumer.',
   edges:[['iutiii:IUTIII.HULL.DET_LOG_VOLUME','statement'],['e-deep:E2.detScalingLaws','proof']] }
];
for(const a of adds){
  if(j.nodes.some(n=>n.id===a.id)) continue;
  j.nodes.push({id:a.id,kind:a.kind,title:a.title,status:'CONDITIONAL',files:[a.file],declarations:{[a.file]:a.decls},note:a.note});
  for(const [to,kind] of a.edges) j.edges.push({from:a.id,to,kind,evidence:'observed_source'});
}
writeFileSync(p, JSON.stringify(j,null,2));
const extra=ROOT+'/dag/watchdog/extra-targets.txt';
let cur=readFileSync(extra,'utf8');
for(const a of adds){ if(!cur.includes(a.file)){ appendFileSync(extra, a.file+'\n'); cur+=a.file+'\n'; } }
console.log('my nodes='+j.nodes.length+' edges='+j.edges.length);
