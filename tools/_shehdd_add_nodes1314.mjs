import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const adds=[
 { id:'ind1-quotient-consumer', title:'(Ind1) formal-quotient consumer laws (projection/lift/uniqueness)',
   file:'tmp/sheaf/xif/paper/ShehddInd1QuotientConsumerActual.lean',
   decls:['ind1_quotient_absorbs','ind1_lift_mk','ind1_lift_unique','ind1QuotientRows','ind1QuotientRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Reuses Ind1Reduction quotient transport laws; IUT source procession/Aut carriers remain NAMED (Ind1 audit note).',
   edges:[['iutiii:IUTIII.IND1','statement'],['iut-skeleton:Ind1','proof']] },
 { id:'abc-logbound-form', title:'ABC log-bound <=> radical-power form consumer',
   file:'tmp/sheaf/xif/paper/ShehddABCLogBoundFormActual.lean',
   decls:['abcLogBound_rpow_consumer','abcLogConjecture_iff_rpow','abcConjecture_iff_rpow','radical_log_weight_consumer','abcLogBoundFormRows','abcLogBoundFormRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Composes LogarithmicBoundEquivalence per-epsilon rpow equivalence + IUTToABC log equivalence; no new assumptions.',
   edges:[['T6-abc-log-form','statement'],['T0-abc-target','proof']] }
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
