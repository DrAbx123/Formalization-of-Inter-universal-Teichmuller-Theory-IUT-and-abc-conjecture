import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const d=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const has=(id)=>d.nodes.some(n=>n.id===id);
const adds=[
 { id:'kummer-map-kernel-consumer', title:'classical Kummer map kernel consumer (kernel = n-th powers, root choice)',
   file:'tmp/sheaf/xif/paper/ShehddKummerMapKernelConsumerActual.lean',
   decls:['kummerMap_kernel_consumer','kummer_trivial_and_root_choice_consumer','kummerMapKernelRows','kummerMapKernelRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Reuses KummerGaloisClass classical Kummer injectivity statements (FiniteDimensional+IsGalois context).',
   edgeCands:['iut-pre-abc:Kummer.absolute','iutiii:IUTIII.STEPXI.LOGSHELL_MUN'] },
 { id:'logshell-carrier-consumer', title:'frozen log-shell carrier consumer (inclusions/closure/invScaled/IQSpan)',
   file:'tmp/sheaf/xif/paper/ShehddLogShellCarrierConsumerActual.lean',
   decls:['logShellCarrier_consumer','logShellCarrier_kummer_consumer','logShellCarrierRows','logShellCarrierRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Reuses SourceLogShellCarrier frozen carrier laws.',
   edgeCands:['iut-pre-abc:Kummer.absolute','e-deep:E1.logShellBridge','iutiii:IUTIII.STEPXI.LOGSHELL_MUN'] }
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
