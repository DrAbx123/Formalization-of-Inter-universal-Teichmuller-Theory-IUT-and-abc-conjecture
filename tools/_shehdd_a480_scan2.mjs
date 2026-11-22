import { readFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const d=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
// edges: from module -> imported module? check schema of one edge
const e0=d.edges[0];
console.log('edge sample='+JSON.stringify(e0).slice(0,300));
const nodesById=new Map(d.nodes.map(n=>[n.id,n]));
const label=(id)=>nodesById.get(id)?.file||nodesById.get(id)?.id||id;
const audit=['C3CompleteSourceReduction','C5Native','C9PaperClosure','N8RouteClosure','C1InfiniteUnitQuotientAttempt','C1QuotientConsumerProbe','C3GaloisUnitFixedAttempt','C3SourceGaloisActionAttempt','C3TensorConstruction','C9P6Closure','FiniteObservationHull','IPLFamilyData','NativeC3','P6Bridge','P6ChainA','P6ChainB','P6Comparison','P6EllOutBridgeAttempt','P6IndInvarianceAttempt','P6L','P6RelaxedGlobalReadout','P6SHEInd','P6SourceVolumeCarrierMapAttempt','PaperNormalizedVolume','PaperValuesBoundedReduction','SourceAlgorithmCompatibility','SourceAllowedOutputActualAttempt','SourcePilotApproximation','SourcePilotApproximationIQ','TargetSignature','UnitSphereReadoutDonorActual'].map(n=>'tmp/sheaf/n8/closure/'+n+'.lean');
const auditSet=new Set(audit);
// determine edge direction by matching known imports: check edges where from/to ids map to node ids
const inDeg=new Map(); const extUsers=new Map();
for(const e of d.edges){
  const from=label(e.from), to=label(e.to);
  if(auditSet.has(to)){ if(!inDeg.has(to)) inDeg.set(to,[]); inDeg.get(to).push(from); if(!from.startsWith('tmp/sheaf/n8/')){ if(!extUsers.has(to)) extUsers.set(to,[]); extUsers.get(to).push(from); } }
}
for(const m of audit){
  const users=inDeg.get(m)||[]; const ext=extUsers.get(m)||[];
  const olean=existsSync(ROOT+'/.lake/build/lib/lean/'+m.replace(/\.lean$/,'.olean'));
  console.log('AUDIT '+m.replace('tmp/sheaf/n8/closure/','')+' | olean='+olean+' | users='+users.length+' | external='+ext.length+(ext.length?' | EXT:'+ext.slice(0,3).join(','):''));
}
// repo-route-index data structure
const idx=JSON.parse(readFileSync(ROOT+'/coord/repo-route-index-data.json','utf8'));
console.log('route keys='+JSON.stringify(Object.keys(idx)).slice(0,300));
if(Array.isArray(idx)) console.log('len='+idx.length+' sample='+JSON.stringify(idx[0]).slice(0,800));
