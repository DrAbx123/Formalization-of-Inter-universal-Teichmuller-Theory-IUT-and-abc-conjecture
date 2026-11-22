import { readFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
function lines(f,a,b){ const t=readFileSync(ROOT+'/'+f,'utf8').split('\n'); return t.slice(a-1,b).map((x,i)=>(a+i)+': '+x).join('\n'); }
console.log('=== QPilot qThetaFourTriangleSynthesis 185-250');
console.log(lines('tmp/sheaf/xif/paper/Mzk1QPilotR4Stage5AlignActual.lean',185,250));
console.log('=== HullDetStep3115 cor312 CONCLUSION 156-200');
console.log(lines('tmp/sheaf/xif/paper/Mzk1HullDetStep3115Actual.lean',156,200));
console.log('=== Step3115ComparisonActual 1-90');
console.log(lines('tmp/sheaf/xif/paper/Mzk1Step3115ComparisonActual.lean',1,90));
