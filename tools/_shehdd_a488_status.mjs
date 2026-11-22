import { existsSync } from 'node:fs';
const ROOT='D:/lean';
const files={
 'Cor312ToABCCards':'LeanFormal/IUT/ABCBridge/Bridge/Cor312ToABCCards.lean',
 'ElementaryEstimates':'LeanFormal/IUT/IUTIV/Estimates/ElementaryEstimates.lean',
 'Section1':'LeanFormal/IUT/IUTIV/Estimates/Section1.lean',
 'Section2':'LeanFormal/IUT/IUTIV/Estimates/Section2.lean',
 'ExpEst00':'tmp/sheaf/xif/paper/ExpEst00NamingActual.lean',
 'ExpEst01':'tmp/sheaf/xif/paper/ExpEst01StatementLedgerActual.lean',
 'ExpEst02':'tmp/sheaf/xif/paper/ExpEst02ElementaryEstimatesActual.lean',
 'S3175':'tmp/sheaf/xif/paper/S3175ExpEstAuditActual.lean',
 'ChebyshevExplicit_LANA':'tmp/dsh-oct6-openai-math-survey-20261016/repos/lana/iut/iut-main/Iut/Implication/ChebyshevExplicit.lean',
 'ChebyshevSixfoldProbe':'tmp/chebyshev-sixfold-20261017/ChebyshevSixfoldProbe.lean',
 'CardsSplitted':'tmp/cor312-to-abc-cards-20261016/Cor312ToABCCards.splitted.lean'
};
for(const [k,f] of Object.entries(files)){
  const src=existsSync(ROOT+'/'+f);
  const ole=src&&existsSync(ROOT+'/.lake/build/lib/lean/'+f.replace(/\.lean$/,'.olean'));
  console.log(k+' src='+src+' olean='+ole);
}
