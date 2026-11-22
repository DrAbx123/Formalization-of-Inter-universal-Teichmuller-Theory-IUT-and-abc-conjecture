import { readFileSync, existsSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
function lines(f,a,b){ const t=readFileSync(ROOT+'/'+f,'utf8').split('\n'); return t.slice(a-1,b).map((x,i)=>(a+i)+': '+x).join('\n'); }
console.log('=== Section1 1-85');
console.log(lines('LeanFormal/IUT/IUTIV/Estimates/Section1.lean',1,85));
console.log('=== ExpEst02 full');
console.log(lines('tmp/sheaf/xif/paper/ExpEst02ElementaryEstimatesActual.lean',1,35));
