import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const d=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const has=(id)=>d.nodes.some(n=>n.id===id);
const adds=[
 { id:'oddtheta-shift-norm-chain', title:'odd theta shift/fraction norm-level chain',
   file:'tmp/sheaf/xif/paper/ShehddOddThetaShiftNormChainActual.lean',
   decls:['oddTheta_shift_norm_chain','oddTheta_fraction_norm_chain','oddTheta_fraction_norm_value_chain'],
   note:'PENDING-VERIFY (watchdog compile). New norm-level chain from OddThetaShift/OddThetaNormalization laws (A476: real theorems only).',
   edgeCands:['iutiii:IUTIII.STEPXI.LOGSHELL_MUN'] },
 { id:'signed-label-inverse-chain', title:'signed-label dictionary right-inverse/bijunction chain',
   file:'tmp/sheaf/xif/paper/ShehddSignedLabelInverseChainActual.lean',
   decls:['representative_toFiniteLabel','toFiniteLabel_bijective_chain'],
   note:'PENDING-VERIFY (watchdog compile). New inverse-direction chain from SignedLabelEquiv laws (A476: real theorems only).',
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
