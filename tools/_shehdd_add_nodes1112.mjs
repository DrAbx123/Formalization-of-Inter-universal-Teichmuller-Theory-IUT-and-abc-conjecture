import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const adds=[
 { id:'qparameter-consumer', title:'q-parameter Def 3.1(b) local log bookkeeping consumer',
   file:'tmp/sheaf/xif/paper/ShehddQParameterConsumerActual.lean',
   decls:['qCandidate_log_summary','qCandidate_exp_and_abs','qCandidate_pow_magnitude','selected_q_log_summary','qParameterConsumerRows','qParameterConsumerRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Reuses ArithmeticQPilotLogVolume/BaseChange q-parameter laws; all-bad-places identification stays repo-current-limit per tree docstring.',
   edges:[['iut-pre-abc:QPilot','statement'],['iut-skeleton:QPilot','proof']] },
 { id:'hull-ob9-consumer', title:'H7/Ob9 two-sided implies one-sided consumer bridge',
   file:'tmp/sheaf/xif/paper/ShehddHullOb9ConsumerActual.lean',
   decls:['hull_ob9_onesided_of_twosided','hull_ob9_twosided_full','hullOb9ConsumerRows','hullOb9ConsumerRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Composes Hull12 one-sided transfer + Hull13 one-sided/two-sided consumers; deep arbitrary-iterate independence remains NAMED.',
   edges:[['e-deep:E3.twoSided','statement'],['e-deep:E3.oneSided','proof']] }
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
