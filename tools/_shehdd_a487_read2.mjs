import { readFileSync, existsSync, statSync } from 'node:fs';
const ROOT='D:/lean';
function lines(f,a,b){ const t=readFileSync(ROOT+'/'+f,'utf8').split('\n'); return t.slice(a-1,b).map((x,i)=>(a+i)+': '+x).join('\n'); }
console.log('=== HullDetFourTriangle 60-100');
console.log(lines('tmp/sheaf/xif/paper/Mzk1HullDetFourTriangleActual.lean',60,100));
console.log('=== olean freshness ===');
for(const n of ['Mzk1FourTriangleSharedActual','Mzk1R4LiteralAssemblyActual','Mzk1Step3115ComparisonActual','Mzk1Step3115WiringActual','Mzk1HullDetStep3115Actual','Mzk1HullDetFourTriangleActual']){
  const f='tmp/sheaf/xif/paper/'+n+'.lean'; const o=ROOT+'/.lake/build/lib/lean/'+f.replace(/\.lean$/,'.olean');
  console.log(n+' src='+(existsSync(ROOT+'/'+f)?statSync(ROOT+'/'+f).mtime.toISOString().slice(11,19):'-')+' olean='+(existsSync(o)?statSync(o).mtime.toISOString().slice(11,19):'miss'));
}
