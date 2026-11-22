import { readFileSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
const ROOT='D:/lean';
function walk(d,out){ let e=[]; try{e=readdirSync(d,{withFileTypes:true})}catch{ return out; } for(const x of e){ if(x.name==='.lake'||x.name==='.git'||x.name==='.lean-shadow') continue; const p=join(d,x.name); if(x.isDirectory()) walk(p,out); else if(x.name.endsWith('.lean')) out.push(p); } return out; }
function strip(s){ return s.replace(/\/\-[^-][\s\S]*?-\//g,'').replace(/--[^\n]*/g,'').replace(/"(?:[^"\\]|\\.)*"/g,'""'); }
const dirs=['LeanFormal/IUT','LeanFormal','tmp/sheaf/xif/paper','tmp/sheaf','Iut'];
const kw=[['ThetaLink',/\b(ThetaLink|ThetaLogLink|thetaLink|LogLink|LogChain)\b/],['Lattice',/\b(LogThetaLattice|Lattice|logThetaLattice)\b/],['Hodge',/\b(HodgeTheater|Hodge)\b/],['LogShell',/\b(LogShell|logShell|LogShellFamily)\b/],['Indet',/\b(Indeterminacy|Ind1|Ind2|Ind3)\b/],['Multiradial',/\b(Multiradial|multiradial)\b/],['InitTheta',/\b(InitialThetaData|InitialTheta)\b/],['Pilot',/\b(QPilot|qPilot|ThetaPilot|thetaPilot|Pilot)\b/],['HullDet',/\b(HullDet|hullDet|HDD|SHE|dsc|DScaling)\b/],['Cor312',/\b(Cor312|Corollary312|Corollary3_12|Thm311|Theorem311)\b/]];
for(const d of dirs){ const files=walk(join(ROOT,d),[]); if(!files.length) continue;
 const counts={}; const samples={}; let defs=0;
 for(const f of files){ let s=''; try{ s=readFileSync(f,'utf8'); }catch{ continue; } const lines=s.split(/\r?\n/);
  for(let i=0;i<lines.length;i++){ const L=lines[i]; if(/^(structure|def|abbrev|class|inductive)\s+/.test(L)){ defs++; for(const [k,re] of kw){ if(re.test(L)){ counts[k]=(counts[k]||0)+1; if(!samples[k]) samples[k]=[]; if(samples[k].length<3) samples[k].push(f.replace(ROOT+'/','')+':'+(i+1)+': '+L.trim().slice(0,120)); } } } }
 }
 console.log('## '+d+' files='+files.length+' defs='+defs+' :: '+JSON.stringify(counts));
 for(const [k,v] of Object.entries(samples)){ for(const s of v) console.log('   ['+k+'] '+s); }
}