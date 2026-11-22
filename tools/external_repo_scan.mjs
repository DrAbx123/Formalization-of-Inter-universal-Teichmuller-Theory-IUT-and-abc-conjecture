import { readFileSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
const ROOT='D:/lean';
const skip=new Set(['.lake','.git','.lean-shadow','node_modules']);
function walk(d,out){ let e=[]; try{e=readdirSync(d,{withFileTypes:true})}catch{ return out; } for(const x of e){ if(skip.has(x.name)) continue; const p=join(d,x.name); if(x.isDirectory()) walk(p,out); else if(x.name.endsWith('.lean')) out.push(p); } return out; }
const base=join(ROOT,'tmp/external');
const dirs=readdirSync(base,{withFileTypes:true}).filter(e=>e.isDirectory()).map(e=>e.name);
console.log('external repos',dirs.length);
const kw=[['ThetaLink',/\b(ThetaLink|ThetaLogLink|thetaLink)\b/],['LogLink',/\b(LogLink|logLink)\b/],['Hodge',/\b(HodgeTheater|Hodge)\b/],['DData',/\b(DData|DPrime|DLess|DGreater|DColumn)\b/],['ellNF',/\b(ellNF|EllNF|lNF)\b/],['Ind',/\b(Ind1|Ind2|Ind3)\b/],['ThetaPilot',/\b(ThetaPilot|thetaPilot)\b/],['QPilot',/\b(QPilot|qPilot)\b/],['Hull',/\b(hull|Hull)\b/],['Multiradial',/\b(Multiradial|multiradial)\b/]];
for(const d of dirs){ const p=join(base,d); const files=walk(p,[]); if(files.length===0) continue; const counts={}; let total=0;
 for(const f of files){ let s=''; try{ s=readFileSync(f,'utf8'); }catch{ continue; } total++; for(const [n,re] of kw){ if(re.test(s)){ counts[n]=(counts[n]||0)+1; } } }
 const nz=Object.entries(counts).filter(([k,v])=>v>0); if(nz.length) console.log(d+' files='+files.length+' :: '+nz.map(([k,v])=>k+'='+v).join(' '));
}