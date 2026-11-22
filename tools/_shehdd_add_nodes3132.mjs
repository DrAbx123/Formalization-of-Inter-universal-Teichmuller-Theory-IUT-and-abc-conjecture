import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const d=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const has=(id)=>d.nodes.some(n=>n.id===id);
const adds=[
 { id:'genell-consumer', title:'GenEll Thm 2.1 / IUT IV §2 / H6xMzk1 consumer bundle',
   file:'tmp/sheaf/xif/paper/ShehddGenEllConsumerActual.lean',
   decls:['genEll_theorem21_iff_consumer','genEll_section2_cor23_consumer','genEll_abcAll_consumer','h6_mzk1_interface_consumer','genEllConsumerRows','genEllConsumerRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Reuses GenEll05/09/10b proved conditionals; paper-input directions stay named.',
   edges:[['e-deep:E5.genEllConsumer','statement'],['e-deep:E5.genEllReduction','proof'],['T0-abc-target','proof']] },
 { id:'tauceti-alignment-consumer', title:'Tau Ceti / log-form ABC alignment consumer',
   file:'tmp/sheaf/xif/paper/ShehddTauCetiAlignmentConsumerActual.lean',
   decls:['tauCeti_iff_abcLogConjecture','radical_aliases_consumer','tauCeti_nat_form_consumer','tauCetiAlignmentRows','tauCetiAlignmentRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Reuses AbcStatementAlignmentActual + LogarithmicBoundEquivalence radical/log equivalences.',
   edges:[['mainline:abc-tau-ceti-alignment','statement'],['mainline:abc-log-equivalence','proof']] }
];
for(const a of adds){
  if(j.nodes.some(n=>n.id===a.id)) continue;
  const edges=a.edges.filter(([to])=>has(to));
  const dropped=a.edges.filter(([to])=>!has(to)).map(([to])=>to);
  j.nodes.push({id:a.id,kind:'theorem',title:a.title,status:'CONDITIONAL',files:[a.file],declarations:{[a.file]:a.decls},note:a.note+(dropped.length?(' Dropped unresolved edge targets: '+dropped.join(',')):'')});
  for(const [to,kind] of edges) j.edges.push({from:a.id,to,kind,evidence:'observed_source'});
}
writeFileSync(p, JSON.stringify(j,null,2));
const extra=ROOT+'/dag/watchdog/extra-targets.txt';
let cur=readFileSync(extra,'utf8');
for(const a of adds){ if(!cur.includes(a.file)){ appendFileSync(extra, a.file+'\n'); cur+=a.file+'\n'; } }
console.log('my nodes='+j.nodes.length+' edges='+j.edges.length);
