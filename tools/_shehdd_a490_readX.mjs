import { readFileSync } from 'node:fs';
const ROOT='D:/lean';
const base=ROOT+'/tmp/sheaf/lana/iut/Iut';
function seg(rel,a,b){ const t=readFileSync(base+'/'+rel,'utf8').split('\n'); return t.slice(a-1,b).map((x,i)=>(a+i)+': '+x).join('\n'); }
console.log('=== IdentifiedCopies 160-210');
console.log(seg('Wall/IdentifiedCopies.lean',160,210));
console.log('=== IdentifiedCopies 460-520');
console.log(seg('Wall/IdentifiedCopies.lean',460,520));
console.log('=== QPilotRegion 300-370');
console.log(seg('Wall/QPilotRegion.lean',300,370));
console.log('=== Ind3 120-135 / 250-285');
console.log(seg('Wall/Ind3.lean',120,135));
console.log(seg('Wall/Ind3.lean',250,285));
