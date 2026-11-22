import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const adds=[
 { id:'label-shared-boundary-consumer', title:'finite-label cardinality / zero-label consumer (Cor 4.10(i) label bookkeeping)',
   file:'tmp/sheaf/xif/paper/ShehddLabelSharedBoundaryConsumerActual.lean',
   decls:['signedLabel_cardinality_consumer','nonzeroFiniteLabel_cardinality_consumer','zeroLabel_toFiniteLabel_zero','zeroLabel_weight_zero','labelSharedBoundaryRows','labelSharedBoundaryRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Reuses SourceSharedBoundary/SourceLabelWeightedDiagonal/SignedLabelEquiv label assets. Paper Cor 4.10(i) verbatim label-identification statement not found in declaration index (search evidence in coord/SURVEY-shehdd.md); closest assets are the finite-label dictionary + SourceLogShellInvariantImageIdentification.',
   edges:[['iutiii:IUTIII.STEPXI.LOGSHELL_MUN','statement'],['iut-skeleton:Cor312','proof']] },
 { id:'thetapilot-iq-consumer', title:'one-place Theta-pilot IQ containment consumer (possible image -> IQ packet)',
   file:'tmp/sheaf/xif/paper/ShehddThetaPilotIQConsumerActual.lean',
   decls:['thetaPilot_IQ_containment','thetaPilot_productMap_tprod','thetaPilotIQRows','thetaPilotIQRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Reuses SourceThetaPilotIQContainment (one-place reduction); full all-place paper tensor remains outside current tree scope (docstring).',
   edges:[['iut-pre-abc:Kummer.absolute','statement'],['e-deep:E1.logShellBridge','proof']] }
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
