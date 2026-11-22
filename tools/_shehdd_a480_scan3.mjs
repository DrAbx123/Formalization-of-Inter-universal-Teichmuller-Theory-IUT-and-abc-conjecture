import { readFileSync } from 'node:fs';
const ROOT='D:/lean';
const d=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
console.log('node sample='+JSON.stringify(d.nodes.slice(0,2)).slice(0,400));
const n8nodes=d.nodes.filter(n=>(n.id||'').includes('tmp/sheaf/n8/closure/')).slice(0,3);
console.log('n8 node sample='+JSON.stringify(n8nodes.map(n=>({id:n.id,keys:Object.keys(n)}))).slice(0,500));
const ids=new Set(d.nodes.map(n=>n.id));
console.log('n8 node count='+d.nodes.filter(n=>(n.id||'').includes('tmp/sheaf/n8/')).length);
// audit ids
const audit=['C3CompleteSourceReduction','C5Native','C9PaperClosure','N8RouteClosure','C1InfiniteUnitQuotientAttempt','C1QuotientConsumerProbe','C3GaloisUnitFixedAttempt','C3SourceGaloisActionAttempt','C3TensorConstruction','C9P6Closure','FiniteObservationHull','IPLFamilyData','NativeC3','P6Bridge','P6ChainA','P6ChainB','P6Comparison','P6EllOutBridgeAttempt','P6IndInvarianceAttempt','P6L','P6RelaxedGlobalReadout','P6SHEInd','P6SourceVolumeCarrierMapAttempt','PaperNormalizedVolume','PaperValuesBoundedReduction','SourceAlgorithmCompatibility','SourceAllowedOutputActualAttempt','SourcePilotApproximation','SourcePilotApproximationIQ','TargetSignature','UnitSphereReadoutDonorActual'];
const inDeg=new Map(), ext=new Map();
for(const e of d.edges){ const to=e.to; if(audit.some(a=>to.endsWith('tmp/sheaf/n8/closure/'+a))){ if(!inDeg.has(to)) inDeg.set(to,[]); inDeg.get(to).push(e.from); if(!e.from.includes('tmp/sheaf/n8/')){ if(!ext.has(to)) ext.set(to,[]); ext.get(to).push(e.from); } } }
for(const a of audit){ const id='olean:tmp/sheaf/n8/closure/'+a; const us=inDeg.get(id)||[]; const ex=ext.get(id)||[]; console.log('AUDIT '+a+' | users='+us.length+' | external='+ex.length+(ex.length?' | '+ex.slice(0,3).join(','):'')); }
const idx=JSON.parse(readFileSync(ROOT+'/coord/repo-route-index-data.json','utf8'));
console.log('stats='+JSON.stringify(idx.stats).slice(0,800));
console.log('rows len='+(idx.rows?idx.rows.length:'?')+' uncovered len='+(idx.uncovered?idx.uncovered.length:'?'));
console.log('row sample='+JSON.stringify((idx.rows||[])[0]).slice(0,600));
console.log('uncovered sample='+JSON.stringify((idx.uncovered||[]).slice(0,6)));
