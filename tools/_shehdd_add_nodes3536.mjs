import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const d=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const has=(id)=>d.nodes.some(n=>n.id===id);
const adds=[
 { id:'tate-parameter-unit-consumer', title:'Tate parameter unit / deck action consumer (q-pilot local uniformization)',
   file:'tmp/sheaf/xif/paper/ShehddTateParameterUnitConsumerActual.lean',
   decls:['tateParameterUnit_deck_fixed_consumer','tateParameterUnit_pow_consumer','tateParameterUnitRows','tateParameterUnitRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Reuses TateUniformizationContract unit laws (ne_one/pow/algEquiv_map/deckSubgroup map).',
   edges:[['iut-pre-abc:QPilot','statement'],['iut-skeleton:QPilot','proof']] },
 { id:'kummer-ratio-cocycle-consumer', title:'Kummer ratio Galois cocycle consumer (Gal -> mu_n)',
   file:'tmp/sheaf/xif/paper/ShehddKummerRatioCocycleConsumerActual.lean',
   decls:['kummerRatio_cocycle_consumer','kummerRatioCocycleRows','kummerRatioCocycleRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Reuses KummerGaloisClass kummerRatio/kummerRatioHom laws.',
   edges:[['iut-pre-abc:Kummer.absolute','statement'],['e-deep:E1.logShellBridge','proof']] }
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
