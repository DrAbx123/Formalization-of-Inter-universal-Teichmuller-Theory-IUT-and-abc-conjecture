import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const adds=[
 { id:'stepxi-finite-certificate-consumer', title:'StepXI finite certificate ordered-chain/hull-average consumer',
   file:'tmp/sheaf/xif/paper/ShehddStepXIFiniteCertificateConsumerActual.lean',
   decls:['finiteCertificate_ordered_chain','finiteCertificate_average_le_hull','finiteCertificateRows','finiteCertificateRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Reuses Volume.lean FiniteHull/WeightedValues/StepXIFiniteCertificate; source-facing hull construction remains the tree Obligation note.',
   edges:[['iutiii:IUTIII.HULL.DET_LOG_VOLUME','statement'],['iutiii:IUTIII.HULL.CARD_GEOMETRY','proof']] },
 { id:'frontier-height-consumer', title:'ABCFrontier => bridge interface / per-epsilon height bound / ABC consumer',
   file:'tmp/sheaf/xif/paper/ShehddABCFrontierHeightConsumerActual.lean',
   decls:['frontier_bridgeInterface','frontier_heightBound','frontier_abc_and_heightBound','frontierHeightRows','frontierHeightRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Composes bridgeInterface_of_frontier/abcConjecture_of_frontier with cor312ToABCBridge_heightBound; frontier premise stays a hypothesis.',
   edges:[['T3-abc-frontier','statement'],['T1-cor312-abc-bridge','proof']] }
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
