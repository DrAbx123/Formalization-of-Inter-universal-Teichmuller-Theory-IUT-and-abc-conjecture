import { readFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
function lines(f,a,b){ const t=readFileSync(ROOT+'/'+f,'utf8').split('\n'); return t.slice(a-1,b).map((x,i)=>(a+i)+': '+x).join('\n'); }
console.log('=== Cor312ToABCCards 40-140');
console.log(lines('LeanFormal/IUT/ABCBridge/Bridge/Cor312ToABCCards.lean',40,140));
console.log('=== Cor312ToABCCards 243-330');
console.log(lines('LeanFormal/IUT/ABCBridge/Bridge/Cor312ToABCCards.lean',243,330));
