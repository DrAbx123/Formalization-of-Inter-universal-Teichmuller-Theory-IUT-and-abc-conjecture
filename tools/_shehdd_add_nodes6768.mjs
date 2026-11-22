import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const d=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const has=(id)=>d.nodes.some(n=>n.id===id);
const adds=[
 { id:'bad-support-chain', title:'odd bad-prime support nonemptiness/valuation chain',
   file:'tmp/sheaf/xif/paper/ShehddBadSupportChainActual.lean',
   decls:['abcOddBadPrimeSupport_chain','odd_bad_prime_valuation_chain','exists_odd_prime_valuation_neg_chain'],
   note:'PENDING-VERIFY (watchdog compile). New chain from ABCNonemptyOddBadSupport laws (A476: real theorems only).',
   edgeCands:['mainline:frey-odd-reduction','T3-abc-frontier'] },
 { id:'primitive-triple-chain', title:'ABC primitive-triple radical chain (coprime + multiplicative + positive)',
   file:'tmp/sheaf/xif/paper/ShehddPrimitiveTripleChainActual.lean',
   decls:['abcTriple_radical_chain','radical_cast_pos_chain'],
   note:'PENDING-VERIFY (watchdog compile). New chain from PrimitiveTriple radical laws + natRadical alias (A476: real theorems only).',
   edgeCands:['T0-abc-target','mainline:abc-invariant-radical-bridge'] }
];
for(const a of adds){
  if(j.nodes.some(n=>n.id===a.id)) continue;
  const edges=[];
  for(const cand of a.edgeCands){ if(has(cand)&&!edges.some(([t])=>t===cand)) edges.push([cand, edges.length===0?'statement':'proof']); }
  j.nodes.push({id:a.id,kind:'theorem',title:a.title,status:'CONDITIONAL',files:[a.file],declarations:{[a.file]:a.decls},note:a.note});
  for(const [to,kind] of edges) j.edges.push({from:a.id,to,kind,evidence:'observed_source'});
}
writeFileSync(p, JSON.stringify(j,null,2));
const extra=ROOT+'/dag/watchdog/extra-targets.txt';
let cur=readFileSync(extra,'utf8');
for(const a of adds){ if(!cur.includes(a.file)){ appendFileSync(extra, a.file+'\n'); cur+=a.file+'\n'; } }
console.log('my nodes='+j.nodes.length+' edges='+j.edges.length);
