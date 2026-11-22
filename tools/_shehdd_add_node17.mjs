import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const a={ id:'etth-gap-consumer', title:'EtTh realization gap / deep-input consumer bridge',
  file:'tmp/sheaf/xif/paper/ShehddEtThGapConsumerActual.lean',
  decls:['etTh_gap_components','etTh_gap_of_components','etTh_realization_holds','etThGapConsumerRows','etThGapConsumerRows_length'],
  note:'PENDING-VERIFY (watchdog compile). Reuses Mzk1EtThGapStatementActual + Mzk1EtThRealizationConsumerActual; GeometricCore remains the single named hypothesis.',
  edges:[['e-deep:E4.etthConsumer','statement'],['e-deep:E4.etthGap','proof']] };
if(!j.nodes.some(n=>n.id===a.id)){
  j.nodes.push({id:a.id,kind:'theorem',title:a.title,status:'CONDITIONAL',files:[a.file],declarations:{[a.file]:a.decls},note:a.note});
  for(const [to,kind] of a.edges) j.edges.push({from:a.id,to,kind,evidence:'observed_source'});
}
writeFileSync(p, JSON.stringify(j,null,2));
const extra=ROOT+'/dag/watchdog/extra-targets.txt';
const cur=readFileSync(extra,'utf8');
if(!cur.includes(a.file)) appendFileSync(extra, a.file+'\n');
console.log('my nodes='+j.nodes.length+' edges='+j.edges.length);
