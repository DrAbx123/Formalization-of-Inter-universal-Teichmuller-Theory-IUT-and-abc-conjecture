import { readFileSync, readdirSync, statSync, existsSync } from 'node:fs';
import { join } from 'node:path';
const ROOT='D:/lean';
function walk(dir,acc){ for(const e of readdirSync(dir,{withFileTypes:true})){ const p=join(dir,e.name); if(e.isDirectory()){ if(e.name==='.lake'||e.name==='.git') continue; walk(p,acc); } else if(e.name.endsWith('.lean')) acc.push(p); } return acc; }
const files=walk(ROOT+'/tmp',[]).concat(walk(ROOT+'/LeanFormal',[])).concat(walk(ROOT+'/Iut',[]));
// imports pointing into n8
const importers={};
for(const f of files){
  if(f.includes('/tmp/sheaf/n8/')) continue;
  const txt=readFileSync(f,'utf8');
  for(const line of txt.split('\n')){
    const m=line.match(/^import tmp\.sheaf\.n8\.(.+)$/);
    if(m){ const mod='tmp/sheaf/n8/'+m[1].replace(/\./g,'/')+'.lean'; if(!importers[mod]) importers[mod]=[]; importers[mod].push(f.replace(ROOT+'/','')); }
  }
}
console.log('externally imported n8 modules: '+Object.keys(importers).length);
for(const [m,fs] of Object.entries(importers)) console.log(m+' <- '+fs.slice(0,4).join(','));
// internal import graph for n8 sorry modules
const audit=['C3CompleteSourceReduction','C5Native','C9PaperClosure','N8RouteClosure','C1InfiniteUnitQuotientAttempt','C1QuotientConsumerProbe','C3GaloisUnitFixedAttempt','C3SourceGaloisActionAttempt','C3TensorConstruction','C9P6Closure','FiniteObservationHull','IPLFamilyData','NativeC3','P6Bridge','P6ChainA','P6ChainB','P6Comparison','P6EllOutBridgeAttempt','P6IndInvarianceAttempt','P6L','P6RelaxedGlobalReadout','P6SHEInd','P6SourceVolumeCarrierMapAttempt','PaperNormalizedVolume','PaperValuesBoundedReduction','SourceAlgorithmCompatibility','SourceAllowedOutputActualAttempt','SourcePilotApproximation','SourcePilotApproximationIQ','TargetSignature','UnitSphereReadoutDonorActual'].map(n=>'tmp/sheaf/n8/closure/'+n+'.lean');
console.log('audit n8 modules='+audit.length);
const auditSet=new Set(audit);
const internalDeps={}, internalUsers={};
for(const f of files){
  if(!f.includes('/tmp/sheaf/n8/closure/')) continue;
  const txt=readFileSync(f,'utf8');
  for(const line of txt.split('\n')){
    const m=line.match(/^import tmp\.sheaf\.n8\.(.+)$/);
    if(m){ const mod='tmp/sheaf/n8/'+m[1].replace(/\./g,'/')+'.lean'; if(auditSet.has(f.replace(ROOT+'/',''))){ if(!internalDeps[f.replace(ROOT+'/','')]) internalDeps[f.replace(ROOT+'/','')]=[]; internalDeps[f.replace(ROOT+'/','')].push(mod); } if(auditSet.has(mod)){ if(!internalUsers[mod]) internalUsers[mod]=[]; internalUsers[mod].push(f.replace(ROOT+'/','')); } }
  }
}
for(const m of audit){
  const ext=importers[m]||[];
  const users=internalUsers[m]||[];
  const o=m.replace(/\.lean$/,'.olean');
  const olean=existsSync(ROOT+'/.lake/build/lib/lean/'+o);
  console.log('AUDIT '+m.replace('tmp/sheaf/n8/closure/','')+' | olean='+olean+' | external='+ext.length+' | internalUsers='+users.length+(ext.length?' | EXT: '+ext.slice(0,3).join(','):''));
}
// repo-route-index structure
const idx=JSON.parse(readFileSync(ROOT+'/coord/repo-route-index-data.json','utf8'));
console.log('--- repo-route-index keys='+JSON.stringify(Object.keys(idx)));
if(Array.isArray(idx)){ console.log('len='+idx.length+' sample='+JSON.stringify(idx[0])); }
else { for(const k of Object.keys(idx)){ const v=idx[k]; console.log(k+' type='+(Array.isArray(v)?('array len='+v.length):typeof v)); } }
