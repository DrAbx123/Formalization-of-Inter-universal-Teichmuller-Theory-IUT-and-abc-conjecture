import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const d=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const has=(id)=>d.nodes.some(n=>n.id===id);
const adds=[
 { id:'hodge-family-laws-consumer', title:'Hodge theater family laws consumer (theta packet constancy/distinctness)',
   file:'tmp/sheaf/xif/paper/ShehddHodgeFamilyLawsConsumerActual.lean',
   decls:['family_thetaPacket_eq_consumer','family_distinct_consumer','hodgeFamilyLawsRows','hodgeFamilyLawsRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Reuses SourceHodgeTheaterFamilyLawsReduction laws.',
   edgeCands:['iut-pre-abc:HodgeTheater.family','iut-skeleton:HodgeTheater','iutiii:IUTIII.STEPXI.LOGSHELL_MUN'] },
 { id:'elliptic-torsion-galois-consumer', title:'elliptic torsion Galois-action consumer (point action + l-torsion representation)',
   file:'tmp/sheaf/xif/paper/ShehddEllipticTorsionGaloisConsumerActual.lean',
   decls:['galoisActionOnPoint_hom_consumer','ltorsion_galois_representation_consumer','ellipticTorsionRows','ellipticTorsionRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Reuses EllipticTorsion Galois-action/representation assets (IUT I Def 3.1(b) layer).',
   edgeCands:['iut-pre-abc:Kummer.absolute','iut-skeleton:QPilot','iutiii:IUTIII.STEPXI.LOGSHELL_MUN'] }
];
for(const a of adds){
  if(j.nodes.some(n=>n.id===a.id)) continue;
  const edges=[];
  for(const cand of a.edgeCands){ if(has(cand)) edges.push([cand, edges.length===0?'statement':'proof']); }
  j.nodes.push({id:a.id,kind:'theorem',title:a.title,status:'CONDITIONAL',files:[a.file],declarations:{[a.file]:a.decls},note:a.note});
  for(const [to,kind] of edges) j.edges.push({from:a.id,to,kind,evidence:'observed_source'});
  if(edges.length<2) j.nodes[j.nodes.length-1].note+=' (only '+edges.length+' existing target node(s) attached)';
}
writeFileSync(p, JSON.stringify(j,null,2));
const extra=ROOT+'/dag/watchdog/extra-targets.txt';
let cur=readFileSync(extra,'utf8');
for(const a of adds){ if(!cur.includes(a.file)){ appendFileSync(extra, a.file+'\n'); cur+=a.file+'\n'; } }
console.log('my nodes='+j.nodes.length+' edges='+j.edges.length);
