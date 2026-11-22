import { readFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const files=[
 'LeanFormal/IUT/ABCBridge/Bridge/Cor312ToABCCards.lean',
 'tmp/sheaf/xif/paper/ExpEst00NamingActual.lean',
 'tmp/sheaf/xif/paper/ExpEst01StatementLedgerActual.lean',
 'tmp/sheaf/xif/paper/ExpEst02ElementaryEstimatesActual.lean',
 'tmp/sheaf/xif/paper/S3175ExpEstAuditActual.lean',
 'tmp/dsh-oct6-openai-math-survey-20261016/repos/lana/iut/iut-main/Iut/Implication/ChebyshevExplicit.lean'
];
for(const f of files){
  const p=ROOT+'/'+f;
  console.log('===== '+f+' src='+existsSync(p));
  if(!existsSync(p)) continue;
  const olean=existsSync(ROOT+'/.lake/build/lib/lean/'+f.replace(/\.lean$/,'.olean'));
  console.log('  olean='+olean);
  const t=readFileSync(p,'utf8').split('\n');
  for(let i=0;i<t.length;i++){
    const s=t[i];
    if(/^(structure|theorem|def|abbrev|noncomputable def|class) /.test(s)){ let acc=s.trim(); let j=i+1; while(j<t.length&&j<i+12&&!/:=|where|:=$/.test(t[j])){ acc+=' '+t[j].trim(); j++; } console.log('  L'+(i+1)+': '+acc.slice(0,300)); }
  }
}
