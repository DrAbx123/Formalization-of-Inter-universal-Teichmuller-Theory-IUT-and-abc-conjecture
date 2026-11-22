import { spawnSync } from 'node:child_process';
const targets=[
'tmp/external/ported/flt/FLT/FreyCurve/FreyPackage.lean',
'tmp/external/ported/flt/FLT/Deformations/RepresentationTheory/GaloisRep.lean',
'tmp/external/ported/flt/FLT/Deformations/RepresentationTheory/GaloisRepFamily.lean',
'tmp/external/ported/flt/FLT/GaloisRepresentation/Automorphic.lean'
];
for(const t of targets){
  console.log('########## TARGET '+t);
  const r=spawnSync(process.execPath,['tools/a836_chain.mjs',t],{cwd:'D:/lean',encoding:'utf8',timeout:3600000,maxBuffer:64*1024*1024});
  console.log('EXIT='+r.status);
  console.log(((r.stdout||'')+(r.stderr||'')).slice(-4000));
}