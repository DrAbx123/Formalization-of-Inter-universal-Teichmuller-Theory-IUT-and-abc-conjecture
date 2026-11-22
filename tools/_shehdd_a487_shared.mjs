import { readFileSync, existsSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const olean=f=>existsSync(ROOT+'/.lake/build/lib/lean/'+f.replace(/\.lean$/,'.olean'));
const shared='tmp/sheaf/xif/paper/Mzk1FourTriangleSharedActual.lean';
console.log('Shared src='+existsSync(ROOT+'/'+shared)+' olean='+olean(shared));
// imports of Shared / old interfaces
const dir=ROOT+'/tmp/sheaf/xif/paper';
for(const f of readdirSync(dir)){
  if(!f.endsWith('.lean')) continue;
  const p=dir+'/'+f;
  const t=readFileSync(p,'utf8');
  if(t.includes('Mzk1FourTriangleSharedActual')&&f!=='Mzk1FourTriangleSharedActual.lean') console.log('imports Shared: '+f);
}
console.log('--- hull files still A? ---');
for(const n of ['Mzk1HullDetStep3115Actual','Mzk1HullDetFourTriangleActual']){
  const p=dir+'/'+n+'.lean';
  if(!existsSync(p)){ console.log(n+' NO-SRC'); continue; }
  const t=readFileSync(p,'utf8');
  console.log(n+' | Shared='+t.includes('Mzk1FourTriangleSharedActual')+' A(FourTriangleSynthesisActual)='+t.includes('Mzk1FourTriangleSynthesisActual')+' R4='+t.includes('Mzk1R4LiteralAssemblyActual'));
}
