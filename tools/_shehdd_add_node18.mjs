import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const a={ id:'k1k2-boundary-consumer', title:'K1/K2 ray-presentation boundary + source vertical realization consumer',
  file:'tmp/sheaf/xif/paper/ShehddK1K2BoundaryConsumerActual.lean',
  decls:['raypresentation_univ_consumer','negLogVolume_hind3_consumer','k1_boundary_of_negLogVolume_ray','k1k2BoundaryRows','k1k2BoundaryRows_length'],
  note:'PENDING-VERIFY (watchdog compile). Reuses Theorem311/SourceK1K2CardReduction proved boundary assembly (h=-logVolume ray presentation).',
  edges:[['iut-skeleton:K1K2','statement'],['iutiii:IUTIII.THM311.OUTPUT_ALGORITHM','proof']] };
if(!j.nodes.some(n=>n.id===a.id)){
  j.nodes.push({id:a.id,kind:'theorem',title:a.title,status:'CONDITIONAL',files:[a.file],declarations:{[a.file]:a.decls},note:a.note});
  for(const [to,kind] of a.edges) j.edges.push({from:a.id,to,kind,evidence:'observed_source'});
}
writeFileSync(p, JSON.stringify(j,null,2));
const extra=ROOT+'/dag/watchdog/extra-targets.txt';
const cur=readFileSync(extra,'utf8');
if(!cur.includes(a.file)) appendFileSync(extra, a.file+'\n');
console.log('my nodes='+j.nodes.length+' edges='+j.edges.length);
