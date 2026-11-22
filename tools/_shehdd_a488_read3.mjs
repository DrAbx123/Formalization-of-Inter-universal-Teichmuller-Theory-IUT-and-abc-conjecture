import { readFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
function lines(f,a,b){ const t=readFileSync(ROOT+'/'+f,'utf8').split('\n'); return t.slice(a-1,b).map((x,i)=>(a+i)+': '+x).join('\n'); }
console.log('=== Cards 140-243');
console.log(lines('LeanFormal/IUT/ABCBridge/Bridge/Cor312ToABCCards.lean',140,243));
console.log('=== Cards 328-400');
console.log(lines('LeanFormal/IUT/ABCBridge/Bridge/Cor312ToABCCards.lean',328,400));
console.log('=== ExpEst01 full');
console.log(lines('tmp/sheaf/xif/paper/ExpEst01StatementLedgerActual.lean',1,60));
