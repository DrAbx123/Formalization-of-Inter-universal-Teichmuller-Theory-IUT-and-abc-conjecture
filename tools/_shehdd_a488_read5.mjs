import { readFileSync } from 'node:fs';
const ROOT='D:/lean';
function lines(f,a,b){ const t=readFileSync(ROOT+'/'+f,'utf8').split('\n'); return t.slice(a-1,b).map((x,i)=>(a+i)+': '+x).join('\n'); }
console.log('=== ElementaryEstimates 70-165');
console.log(lines('LeanFormal/IUT/IUTIV/Estimates/ElementaryEstimates.lean',70,165));
console.log('=== Section2 all decl names ===');
const t=readFileSync(ROOT+'/LeanFormal/IUT/IUTIV/Estimates/Section2.lean','utf8').split('\n');
for(let i=0;i<t.length;i++){ if(/^(theorem|lemma|def) /.test(t[i])){ let acc=t[i].trim(); let j=i+1; while(j<t.length&&j<i+8&&!/:=|where/.test(t[j])){ acc+=' '+t[j].trim(); j++; } console.log('  L'+(i+1)+': '+acc.slice(0,250)); } }
