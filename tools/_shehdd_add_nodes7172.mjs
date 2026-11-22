import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const d=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const has=(id)=>d.nodes.some(n=>n.id===id);
const adds=[
 { id:'qnorm-power-chain', title:'Tate q-norm power-decay chain',
   file:'tmp/sheaf/xif/paper/ShehddQNormPowerChainActual.lean',
   decls:['qNorm_bounds_chain','exp_log_qNorm_chain','qNorm_pow_succ_lt_chain'],
   note:'PENDING-VERIFY (watchdog compile). New chain from TateCurvePadicEstimates q-norm laws (A476: real theorems only).',
   edgeCands:['iut-pre-abc:QPilot','iut-skeleton:QPilot'] },
 { id:'qcandidate-pow-chain', title:'q-candidate positive-power contraction chain',
   file:'tmp/sheaf/xif/paper/ShehddQCandidatePowChainActual.lean',
   decls:['qCandidate_pow_chain','qCandidate_pow_norm_chain'],
   note:'PENDING-VERIFY (watchdog compile). New chain from FinitePlaceQCandidate data + q-norm estimates (A476: real theorems only).',
   edgeCands:['iut-pre-abc:QPilot','iut-skeleton:QPilot'] }
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
