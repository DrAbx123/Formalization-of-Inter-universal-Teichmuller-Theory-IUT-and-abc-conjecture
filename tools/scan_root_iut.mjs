import { readFileSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
const ROOT='D:/lean';
function walk(d,out){ let e=[]; try{e=readdirSync(d,{withFileTypes:true})}catch{ return out; } for(const x of e){ if(x.name==='.lake'||x.name==='.git') continue; const p=join(d,x.name); if(x.isDirectory()) walk(p,out); else if(x.name.endsWith('.lean')) out.push(p); } return out; }
function strip(s){ return s.replace(/\/\-[^-][\s\S]*?-\//g,'').replace(/--[^\n]*/g,'').replace(/"(?:[^"\\]|\\.)*"/g,'""'); }
const files=walk(join(ROOT,'Iut'),[]);
console.log('root Iut files',files.length);
let sorry=0; const sorryFiles=[];
const kw=[['HodgeTheater',/\b(HodgeTheater|Hodge)\b/],['LogShell',/\b(LogShell|LogLink)\b/],['ThetaLink',/\b(ThetaLink|ThetaLogLink|logLink)\b/],['Lattice',/\b(LogThetaLattice|Lattice)\b/],['Indeterminacy',/\b(Indeterminacy|Ind1|Ind2|Ind3)\b/],['Multiradial',/\b(Multiradial|multiradial)\b/],['InitialThetaData',/\b(InitialThetaData|InitialTheta)\b/],['Region',/\b(RegionMeasure|Procession|Region)\b/],['Cor312',/\b(Cor312|Corollary312|Corollary3_12)\b/],['Thm311',/\b(Thm311|Theorem311)\b/],['ABC',/\b(ABC|Abc|abc)\b/],['Hull',/\b(Hull|hull)\b/],['QPilot',/\b(QPilot|qPilot|Pilot)\b/]];
const counts={};
for(const f of files){ let s=''; try{ s=readFileSync(f,'utf8'); }catch{ continue; } const st=strip(s); const n=(st.match(/\bsorry\b|\badmit\b/g)||[]).length; if(n){ sorry+=n; sorryFiles.push([f.replace(ROOT+'/',''),n]); } for(const [k,re] of kw){ if(re.test(s)) counts[k]=(counts[k]||0)+1; } }
console.log('codeSorry',sorry,'files',sorryFiles.length); for(const [f,n] of sorryFiles.slice(0,8)) console.log('  sorry',f,n);
console.log(JSON.stringify(counts));