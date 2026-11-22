import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const d=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const has=(id)=>d.nodes.some(n=>n.id===id);
const adds=[
 { id:'oddtheta-algebra-chain', title:'odd theta exponent/sign/coefficient algebra and tsum reindexing chain',
   file:'tmp/sheaf/xif/paper/ShehddOddThetaAlgebraChainActual.lean',
   decls:['oddThetaExponent_double_chain','oddThetaSign_algebra_chain','oddTheta_root_coefficient_chain','oddTheta_tsum_reindex_chain'],
   note:'PENDING-VERIFY (watchdog compile). New chain from OddThetaTermAlgebra/OddThetaShiftSum laws (A476: real theorems only).',
   edgeCands:['iutiii:IUTIII.STEPXI.LOGSHELL_MUN'] },
 { id:'signed-label-neg-chain', title:'signed label negation/theta evenness chain',
   file:'tmp/sheaf/xif/paper/ShehddSignedLabelNegChainActual.lean',
   decls:['signedLabel_neg_theta_chain','signedLabel_toFl_neg_chain','signedLabel_neg_val_chain'],
   note:'PENDING-VERIFY (watchdog compile). New chain from SignedLabel negation/Gaussian theta laws (A476: real theorems only).',
   edgeCands:['iutiii:IUTIII.STEPXI.LOGSHELL_MUN'] }
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
