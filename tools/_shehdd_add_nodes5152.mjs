import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const d=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const has=(id)=>d.nodes.some(n=>n.id===id);
const adds=[
 { id:'local-log-inverse-consumer', title:'local logarithm inverse/preimage consumer (log1p ball, scale bounds, integral logShell)',
   file:'tmp/sheaf/xif/paper/ShehddLocalLogInverseConsumerActual.lean',
   decls:['log1p_preimage_consumer','logShellScale_bounds_consumer','norm_one_add_consumer','unitLog_surjective_consumer','integers_subset_integralLogShell_consumer','localLogInverseRows','localLogInverseRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Reuses LogarithmLocalInverse analytic inverse laws (ProperSpace section for integral log-shell).',
   edgeCands:['e-deep:E1.logShellBridge','iutiii:IUTIII.STEPXI.LOGSHELL_MUN'] },
 { id:'integral-unit-log-consumer', title:'integral unit logarithm consumer (mul/pow/principal/exponent independence)',
   file:'tmp/sheaf/xif/paper/ShehddIntegralUnitLogConsumerActual.lean',
   decls:['unitLog_hom_consumer','unitLog_principal_consumer','unitLog_exponent_independence_consumer','integralUnitLogRows','integralUnitLogRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Reuses IntegralUnitLogarithm constructed unitLog laws.',
   edgeCands:['e-deep:E1.logShellBridge','iutiii:IUTIII.STEPXI.LOGSHELL_MUN'] }
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
