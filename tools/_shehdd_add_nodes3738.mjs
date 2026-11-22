import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const d=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const has=(id)=>d.nodes.some(n=>n.id===id);
const firstExisting=(ids)=>{ for(const id of ids){ if(has(id)) return id; } return null; };
const adds=[
 { id:'theta-displacement-consumer', title:'theta-link displacement consumer (q/scale displacement + equivalence)',
   file:'tmp/sheaf/xif/paper/ShehddThetaDisplacementConsumerActual.lean',
   decls:['thetaDisplacement_link_consumer','thetaDisplacement_equivalence_consumer','thetaDisplacementRows','thetaDisplacementRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Reuses SourceThetaLinkDisplacementReduction displacement laws.',
   edgeCands:['iut-pre-abc:HodgeTheater.family','iut-skeleton:HodgeTheater','iutiii:IUTIII.STEPXI.LOGSHELL_MUN'] },
 { id:'kummer-roots-consumer', title:'Kummer roots / absolute-Galois fixed points consumer',
   file:'tmp/sheaf/xif/paper/ShehddKummerRootsConsumerActual.lean',
   decls:['kummer_root_and_chosenRoot_consumer','absoluteGalois_fixed_mem_base_consumer','kummerRootsRows','kummerRootsRows_length'],
   note:'PENDING-VERIFY (watchdog compile). Reuses AlgebraicClosureKummerRoots + chosenRoot_spec.',
   edgeCands:['iut-pre-abc:Kummer.absolute','iutiii:IUTIII.STEPXI.LOGSHELL_MUN'] }
];
for(const a of adds){
  if(j.nodes.some(n=>n.id===a.id)) continue;
  const edges=[];
  for(const cand of a.edgeCands){ if(has(cand)) edges.push([cand, edges.length===0?'statement':'proof']); }
  j.nodes.push({id:a.id,kind:'theorem',title:a.title,status:'CONDITIONAL',files:[a.file],declarations:{[a.file]:a.decls},note:a.note});
  for(const [to,kind] of edges) j.edges.push({from:a.id,to,kind,evidence:'observed_source'});
  if(edges.length<2) j.nodes[j.nodes.length-1].note+=' (secondary edge candidate had no existing DAG node; only '+edges.length+' edge(s) attached)';
}
writeFileSync(p, JSON.stringify(j,null,2));
const extra=ROOT+'/dag/watchdog/extra-targets.txt';
let cur=readFileSync(extra,'utf8');
for(const a of adds){ if(!cur.includes(a.file)){ appendFileSync(extra, a.file+'\n'); cur+=a.file+'\n'; } }
console.log('my nodes='+j.nodes.length+' edges='+j.edges.length);
