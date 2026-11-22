import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const d=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const has=(id)=>d.nodes.some(n=>n.id===id);
const adds=[
 { id:'norm-log-consumer', title:'norm/log degree consumer (multiplicativity + log norm)',
   file:'tmp/sheaf/xif/paper/ShehddNormLogConsumerActual.lean',
   decls:['unitNormLogDegree_consumer','normLogRows','normLogRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Reuses NormLog unitNormLogDegree laws.',
   edgeCands:['iutiii:IUTIII.STEPXI.LOGSHELL_MUN','e-deep:E1.logShellBridge','iut-pre-abc:Kummer.absolute'] },
 { id:'local-logshell-datum-consumer', title:'actual local log-shell datum consumer (pStar/pre/logShell/integralLogShell)',
   file:'tmp/sheaf/xif/paper/ShehddLocalLogShellDatumConsumerActual.lean',
   decls:['localLogShellDatum_consumer','localLogShellDatumRows','localLogShellDatumRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Reuses SourceLocalLogShellDatum actual common-prime-completion carrier laws.',
   edgeCands:['iut-pre-abc:LogShell.datum','iutiii:IUTIII.STEPXI.LOGSHELL_MUN','e-deep:E1.logShellBridge','iut-pre-abc:Kummer.absolute'] }
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
