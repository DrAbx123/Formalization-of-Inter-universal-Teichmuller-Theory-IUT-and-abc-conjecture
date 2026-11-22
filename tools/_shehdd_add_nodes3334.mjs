import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const d=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const has=(id)=>d.nodes.some(n=>n.id===id);
const cands=[['mainline:abc-invariant-radical-bridge','statement'],['mainline:abc-invariant-coprimality','statement']];
const adds=[
 { id:'absolute-kummer-kernel-consumer', title:'absolute Kummer kernel = n-th powers consumer (kernel/quotient bundle)',
   file:'tmp/sheaf/xif/paper/ShehddAbsoluteKummerKernelConsumerActual.lean',
   decls:['absoluteKummerMap_ker_eq_nthPowerSubgroup','absoluteKummer_kernel_and_quotient_consumer','absoluteKummerKernelRows','absoluteKummerKernelRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Identifies kernel of absoluteKummerMap with nthPowerSubgroup; reuses AbsoluteKummerInjection/Quotient.',
   edges:[['iut-pre-abc:Kummer.absolute','statement'],['iutiii:IUTIII.STEPXI.LOGSHELL_MUN','proof']] },
 { id:'invariant-radical-consumer', title:'ABC invariant radical/log comparison consumer',
   file:'tmp/sheaf/xif/paper/ShehddInvariantRadicalConsumerActual.lean',
   decls:['invariant_den_radical_bounds_consumer','invariant_den_primeFactors_consumer','invariant_den_logRadical_consumer','natRadical_double_consumer','invariantRadicalRows','invariantRadicalRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Reuses ABCInvariantRadicalBridge radical/log comparison laws.',
   edges:[['mainline:abc-invariant-radical-bridge','statement'],['T0-abc-target','proof']] }
];
for(const a of adds){
  if(j.nodes.some(n=>n.id===a.id)) continue;
  let edges=a.edges.filter(([to])=>has(to));
  const dropped=a.edges.filter(([to])=>!has(to)).map(([to])=>to);
  if(a.id==='invariant-radical-consumer'){ const alt=cands.find(([to])=>has(to)); if(alt&&!edges.some(([t])=>t===alt[0])) edges=edges.concat([alt]); }
  j.nodes.push({id:a.id,kind:'theorem',title:a.title,status:'CONDITIONAL',files:[a.file],declarations:{[a.file]:a.decls},note:a.note+(dropped.length?(' Dropped unresolved edge targets: '+dropped.join(',')):'')});
  for(const [to,kind] of edges) j.edges.push({from:a.id,to,kind,evidence:'observed_source'});
}
writeFileSync(p, JSON.stringify(j,null,2));
const extra=ROOT+'/dag/watchdog/extra-targets.txt';
let cur=readFileSync(extra,'utf8');
for(const a of adds){ if(!cur.includes(a.file)){ appendFileSync(extra, a.file+'\n'); cur+=a.file+'\n'; } }
console.log('my nodes='+j.nodes.length+' edges='+j.edges.length);
