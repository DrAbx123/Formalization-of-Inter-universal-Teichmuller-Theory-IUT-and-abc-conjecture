import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const adds=[
 { id:'absolute-kummer-trio-consumer', title:'absolute/etale Kummer trio consumer (kernel criterion + quotient injectivity + local constancy)',
   file:'tmp/sheaf/xif/paper/ShehddAbsoluteKummerTrioConsumerActual.lean',
   decls:['absoluteKummer_trio_summary','nthPowerSubgroup_mem_consumer','absoluteKummerTrioRows','absoluteKummerTrioRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Reuses IUTII/Kummer AbsoluteKummer{Injection,Quotient,Continuity} proved laws.',
   edges:[['iut-pre-abc:Kummer.absolute','statement'],['iutiii:IUTIII.STEPXI.LOGSHELL_MUN','proof']] },
 { id:'frobenius-graphaut-consumer', title:'Frobenius-picture graph automorphism closure + translation classification consumer',
   file:'tmp/sheaf/xif/paper/ShehddFrobeniusGraphAutConsumerActual.lean',
   decls:['frobenius_graphAut_closure_summary','frobenius_graphAut_translation_parameter','frobenius_chainTranslation_injective','frobeniusGraphAutRows','frobeniusGraphAutRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Reuses SourceThetaLinkGraphAutomorphismReduction + Mzk1FrobeniusGraphAutClosureActual group laws.',
   edges:[['iut-pre-abc:FrobeniusPicture.graph','statement'],['iut-pre-abc:FrobeniusPicture.translationClass','proof']] }
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
