import { readFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const queue=new Set(readFileSync(ROOT+'/dag/watchdog/extra-targets.txt','utf8').split('\n').filter(Boolean));
const prio=new Set(readFileSync(ROOT+'/dag/watchdog/priority-files.txt','utf8').split('\n').filter(Boolean));
const olean=f=>existsSync(ROOT+'/.lake/build/lib/lean/'+f.replace(/\.lean$/,'.olean'));
const files=[
 'tmp/sheaf/xif/paper/Mzk1QPilotR4Stage5AlignActual.lean',
 'tmp/sheaf/xif/paper/Mzk1HullDetStep3115Actual.lean',
 'tmp/sheaf/xif/paper/Mzk1Step3115ComparisonActual.lean',
 'tmp/sheaf/xif/paper/Mzk1R4LiteralAssemblyActual.lean',
 'tmp/sheaf/xif/paper/Mzk1R4LiteralAssemblyV2Actual.lean',
 'tmp/sheaf/xif/paper/Mzk1FourTriangleSynthesisActual.lean',
 'tmp/sheaf/xif/paper/Mzk1HDDObjectActual.lean',
 'tmp/sheaf/xif/paper/Mzk1R4EndgameCompositionActual.lean',
 'tmp/sheaf/xif/paper/S650ActualSignedCor312Contract.lean',
 'tmp/sheaf/xif/paper/S650ActualSignedCor312ContractAdapted.lean',
 'LeanFormal/IUT/IUTIII/Corollary312/StepXI/FiniteAlignmentSocketInstance.lean',
 'LeanFormal/IUT/IUTIII/Corollary312/StepXI/FiniteAlignmentStrictSocketInstance.lean'
];
for(const f of files){
  const src=existsSync(ROOT+'/'+f);
  const log='dag/watchdog/logs/'+f.replace(/\//g,'_')+'.log';
  let err='';
  if(existsSync(ROOT+'/'+log)){ const l=readFileSync(ROOT+'/'+log,'utf8').split('\n').find(x=>x.includes(': error')); err=l?l.trim().slice(0,140):''; }
  console.log((src?'SRC ':'----')+' '+(olean(f)?'GREEN':'miss ')+' q='+(queue.has(f)?'1':'0')+' p='+(prio.has(f)?'1':'0')+' | '+f.split('/').pop()+(err?' | ERR: '+err:''));
}
// endgame decls
const eg=readFileSync(ROOT+'/tmp/sheaf/xif/paper/Mzk1R4EndgameCompositionActual.lean','utf8').split('\n');
console.log('=== endgame imports/decls');
for(let i=0;i<eg.length;i++){ const t=eg[i]; if(t.startsWith('import ')) console.log('  imp '+t.slice(7).trim()); else if(/^(theorem|def|structure|abbrev) /.test(t)){ let s=t.trim(); let j=i+1; while(j<eg.length&&j<i+16&&!/:=|where/.test(eg[j])){ s+=' '+eg[j].trim(); j++; } console.log('  L'+(i+1)+': '+s.slice(0,340)); } }
