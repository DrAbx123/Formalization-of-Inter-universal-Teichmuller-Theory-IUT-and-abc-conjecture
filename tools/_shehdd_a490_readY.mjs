import { readFileSync } from 'node:fs';
const ROOT='D:/lean';
const base=ROOT+'/tmp/sheaf/lana/iut/Iut';
function seg(rel,a,b){ const t=readFileSync(base+'/'+rel,'utf8').split('\n'); return t.slice(a-1,b).map((x,i)=>(a+i)+': '+x).join('\n'); }
console.log('=== MultiContainer 80-100'); console.log(seg('Wall/MultiContainer.lean',80,100));
console.log('=== Forms 40-60'); console.log(seg('WallEquiv/Forms.lean',40,60));
console.log('=== Constraints 90-230'); console.log(seg('Wall/Constraints.lean',90,230));
console.log('=== EtaAlg 165-232'); console.log(seg('Wall/EtaAlg.lean',165,232));
