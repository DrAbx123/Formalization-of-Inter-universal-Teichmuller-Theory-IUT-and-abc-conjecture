import { readFileSync, existsSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const iut=ROOT+'/tmp/sheaf/lana/iut';
function walk(x,acc){ for(const e of readdirSync(x,{withFileTypes:true})){ const p=x+'/'+e.name; if(e.isDirectory()) walk(p,acc); else if(e.name.endsWith('.lean')) acc.push(p); } return acc; }
const files=walk(iut,[]);
console.log('ported iut files='+files.length);
for(const pat of [/rhsDataOn_singleton/,/def distinguished/,/ivLabels_nonempty/,/def thetaPilotOn/,/theorem rhs_le_rhsLit/]){
  let n=0;
  for(const f of files){ const t=readFileSync(f,'utf8').split('\n'); for(let i=0;i<t.length;i++){ if(pat.test(t[i])){ console.log(f.replace(ROOT+'/tmp/sheaf/lana/','')+':'+(i+1)+': '+t[i].trim().slice(0,150)); n++; if(n>=4) break; } } if(n>=4) break; }
}
// queue/olean stats for Wall
const q=new Set(readFileSync(ROOT+'/dag/watchdog/extra-targets.txt','utf8').split('\n').filter(Boolean));
const wall=files.filter(f=>f.includes('/Wall/')||f.includes('/WallEquiv/'));
const ole=f=>existsSync(ROOT+'/.lake/build/lib/lean/'+f.replace(ROOT+'/','').replace(/\.lean$/,'.olean'));
console.log('Wall+WallEquiv files='+wall.length+' queued='+wall.filter(f=>q.has(f.replace(ROOT+'/',''))).length+' olean='+wall.filter(ole).length);
