import { readFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
function lines(f,a,b){ const t=readFileSync(ROOT+'/'+f,'utf8').split('\n'); return t.slice(a-1,b).map((x,i)=>(a+i)+': '+x).join('\n'); }
console.log('=== R4LiteralAssemblyActual 25-105');
console.log(lines('tmp/sheaf/xif/paper/Mzk1R4LiteralAssemblyActual.lean',25,105));
console.log('=== FourTriangleSynthesisActual 20-90');
console.log(lines('tmp/sheaf/xif/paper/Mzk1FourTriangleSynthesisActual.lean',20,90));
console.log('=== HDDObjectActual 10-45');
console.log(lines('tmp/sheaf/xif/paper/Mzk1HDDObjectActual.lean',10,45));
