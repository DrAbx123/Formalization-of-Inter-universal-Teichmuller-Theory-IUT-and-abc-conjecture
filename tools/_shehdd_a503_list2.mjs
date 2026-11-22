import { readFileSync, readdirSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/tmp/external/Takkun-IUT_LEAN/IutLean';
function walk(x,acc){ for(const e of readdirSync(x,{withFileTypes:true})){ const q=x+'/'+e.name; if(e.isDirectory()) walk(q,acc); else if(e.name.endsWith('.lean')) acc.push(q.replace(p+'/','')); } return acc; }
const files=walk(p,[]);
console.log(files.slice(40).join('\n'));
console.log('=== structures/defs of interest ===');
const pats=[/structure FhPrimeStrip/,/structure PrimeStripSystem/,/structure PrimeStripData/,/structure LogShell/,/structure LogChain/,/structure LogThetaLattice/,/structure RealHodgeTheater/,/structure HodgeTheater/,/structure InitialThetaData/,/structure ThetaValues|def thetaValue/];
for(const pat of pats){
  let n=0;
  for(const rel of files){ const t=readFileSync(p+'/'+rel,'utf8').split('\n'); for(let i=0;i<t.length;i++){ if(pat.test(t[i])){ console.log(pat+': '+rel+':'+(i+1)+': '+t[i].trim().slice(0,130)); n++; if(n>=3) break; } } if(n>=3) break; }
}
