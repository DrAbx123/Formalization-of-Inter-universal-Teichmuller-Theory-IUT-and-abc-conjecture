import { readFileSync, readdirSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
function walk(x,acc){ for(const e of readdirSync(x,{withFileTypes:true})){ const p=x+'/'+e.name; if(e.isDirectory()){ if(['.lake','.git','logs'].includes(e.name)) continue; walk(p,acc); } else if(e.name.endsWith('.lean')) acc.push(p); } return acc; }
const files=walk(ROOT+'/LeanFormal',[]).concat(walk(ROOT+'/tmp/sheaf',[]));
const pats=[/structure HodgeTheater\b/,/structure HodgeTheaterCore/,/structure HodgeTheaterLink/,/structure ThreeTheaterSystem/,/structure DPrimeStrip|structure DhPrimeStrip|structure DhPrimeStripEquiv/,/structure SourceLogShellCarrier|def logShell\b|structure LogShellFamily|structure SourceSequenceStep/];
for(const p of pats){
  console.log('PATTERN '+p);
  let n=0;
  for(const f of files){ const t=readFileSync(f,'utf8').split('\n'); for(let i=0;i<t.length;i++){ if(p.test(t[i])){ console.log('  '+f.replace(ROOT+'/','')+':'+(i+1)+': '+t[i].trim().slice(0,140)); n++; if(n>=6) break; } } if(n>=6) break; }
}
