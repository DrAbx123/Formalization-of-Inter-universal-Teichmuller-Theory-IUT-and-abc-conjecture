import { readFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const cands=[
 'tmp/sheaf/xif/paper/Mzk1QPilotR4Stage5AlignActual.lean',
 'tmp/sheaf/xif/paper/Mzk1HullDetStep3115Actual.lean',
 'tmp/sheaf/xif/paper/Mzk1Step3115ComparisonActual.lean',
 'tmp/sheaf/xif/paper/Mzk1Step3115WiringActual.lean',
 'tmp/sheaf/xif/paper/Mzk1R4LiteralAssemblyActual.lean',
 'tmp/sheaf/xif/paper/Mzk1R4EndgameCompositionActual.lean',
 'tmp/sheaf/xif/paper/Mzk1HullDetFourTriangleActual.lean',
 'tmp/sheaf/xif/paper/Mzk1QThetaHullDetAlignActual.lean',
 'tmp/sheaf/xif/paper/Mzk1A486WiringActual.lean',
];
for(const f of cands){
  const src=existsSync(ROOT+'/'+f);
  const ole=src&&existsSync(ROOT+'/.lake/build/lib/lean/'+f.replace(/\.lean$/,'.olean'));
  console.log((src?'SRC ':'----')+' '+(ole?'GREEN':'miss ')+' '+f);
}
console.log('--- finite carrier / S650 / S3139 ---');
const { readdirSync, statSync } = await import('node:fs');
for(const dir of [ROOT+'/tmp/sheaf/xif/paper', ROOT+'/LeanFormal/IUT/IUTIII/Corollary312', ROOT+'/LeanFormal/IUT/IUTIII/Corollary312/StepXI']){
  if(!existsSync(dir)) continue;
  for(const f of readdirSync(dir)){
    if(/FiniteAlignment|S650|S3139|FiniteCertificate|Socket/.test(f) && f.endsWith('.lean')){
      const p=dir+'/'+f;
      console.log('  '+p.replace(ROOT+'/','')+' olean='+existsSync(ROOT+'/.lake/build/lib/lean/'+p.replace(ROOT+'/','').replace(/\.lean$/,'.olean')));
    }
  }
}
