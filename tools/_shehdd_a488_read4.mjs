import { readFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
function lines(f,a,b){ const t=readFileSync(ROOT+'/'+f,'utf8').split('\n'); return t.slice(a-1,b).map((x,i)=>(a+i)+': '+x).join('\n'); }
console.log('=== Section1 85-105');
console.log(lines('LeanFormal/IUT/IUTIV/Estimates/Section1.lean',85,105));
console.log('=== Section2 90-135');
console.log(lines('LeanFormal/IUT/IUTIV/Estimates/Section2.lean',90,135));
console.log('=== ChebyshevSixfoldProbe decls + olean');
const f='tmp/chebyshev-sixfold-20261017/ChebyshevSixfoldProbe.lean';
console.log('src='+existsSync(ROOT+'/'+f)+' olean='+existsSync(ROOT+'/.lake/build/lib/lean/'+f.replace(/\.lean$/,'.olean')));
if(existsSync(ROOT+'/'+f)){ const t=readFileSync(ROOT+'/'+f,'utf8').split('\n'); for(let i=0;i<t.length;i++){ if(/^(theorem|def|lemma) /.test(t[i])){ let acc=t[i].trim(); let j=i+1; while(j<t.length&&j<i+10&&!/:=|where/.test(t[j])){ acc+=' '+t[j].trim(); j++; } console.log('  L'+(i+1)+': '+acc.slice(0,260)); } } }
