import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const d=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const has=(id)=>d.nodes.some(n=>n.id===id);
const adds=[
 { id:'oddtheta-term-chain', title:'odd theta backward-term/summability/nonvanishing chain',
   file:'tmp/sheaf/xif/paper/ShehddOddThetaTermChainActual.lean',
   decls:['oddThetaTerm_backward_chain','oddTheta_backward_summable_chain','oddTheta_nonvanishing_chain','oddThetaExponent_lower_bound_chain'],
   note:'PENDING-VERIFY (watchdog compile). New chain from OddTheta term/decay/nonvanishing laws (A476: real theorems only).',
   edgeCands:['iutiii:IUTIII.STEPXI.LOGSHELL_MUN','iut-pre-abc:ThetaLink'] },
 { id:'chosen-root-val-chain', title:'chosen Kummer root field-level power chain',
   file:'tmp/sheaf/xif/paper/ShehddChosenRootValChainActual.lean',
   decls:['chosenRoot_val_pow','root_fixed_mem_base_chain'],
   note:'PENDING-VERIFY (watchdog compile). New field-level chain from chosenRoot_spec/fixed_by_absoluteGalois_mem_base (A476: real theorems only).',
   edgeCands:['iut-pre-abc:Kummer.absolute','iutiii:IUTIII.STEPXI.LOGSHELL_MUN'] }
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
