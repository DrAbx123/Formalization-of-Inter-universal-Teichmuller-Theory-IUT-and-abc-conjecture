import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const d=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const has=(id)=>d.nodes.some(n=>n.id===id);
const adds=[
 { id:'tatej-invariant-norm-consumer', title:'Tate j-invariant norm consumer (||j||=||q||^-1, jΔ=c4^3)',
   file:'tmp/sheaf/xif/paper/ShehddTateJInvariantNormConsumerActual.lean',
   decls:['tateJInvariant_norm_summary','tateJInvariant_norm_pos_and_ne_zero','tateJInvariantNormRows','tateJInvariantNormRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Reuses Foundations/Geometry/TateJInvariantNorm proved norm laws.',
   edges:[['iut-pre-abc:QPilot','statement'],['iut-skeleton:QPilot','proof']] },
 { id:'frontier-shortcut-refuted-consumer', title:'refuted frontier shortcut consumer (F4a + reduced variants empty)',
   file:'tmp/sheaf/xif/paper/ShehddFrontierShortcutRefutedConsumerActual.lean',
   decls:['frontier_shortcuts_refuted','frontier_f4a_counterexample','frontierShortcutRows','frontierShortcutRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Reuses ABCFrontierHeightWeightRefutation + SingletonReduction refutations; unreduced frontier unaffected (equivalent to ABC).',
   edges:[['T3-abc-frontier','statement']] }
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
