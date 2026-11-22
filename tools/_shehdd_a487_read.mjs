import { readFileSync } from 'node:fs';
const ROOT='D:/lean';
for(const f of ['tmp/sheaf/xif/paper/Mzk1R4LiteralAssemblyActual.lean','tmp/sheaf/xif/paper/Mzk1HullDetFourTriangleActual.lean']){
  console.log('===== '+f);
  const t=readFileSync(ROOT+'/'+f,'utf8').split('\n');
  t.forEach((s,i)=>{ if(s.startsWith('import ')||s.startsWith('open ')) console.log((i+1)+': '+s.trim()); });
  console.log('--- decls ---');
  for(let i=0;i<t.length;i++){ if(/^(structure|theorem|def|abbrev|instance) /.test(t[i])){ let acc=t[i].trim(); let j=i+1; while(j<t.length&&j<i+14&&!/:=|where/.test(t[j])){ acc+=' '+t[j].trim(); j++; } console.log('  L'+(i+1)+': '+acc.slice(0,280)); } }
}
