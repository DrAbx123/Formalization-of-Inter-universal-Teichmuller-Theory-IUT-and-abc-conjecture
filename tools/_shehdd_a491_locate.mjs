import { readFileSync, existsSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const iut=ROOT+'/tmp/sheaf/lana/iut/Iut';
function walk(x,acc){ for(const e of readdirSync(x,{withFileTypes:true})){ const p=x+'/'+e.name; if(e.isDirectory()) walk(p,acc); else if(e.name.endsWith('.lean')) acc.push(p); } return acc; }
const all=walk(iut,[]);
for(const pat of [/structure InitialThetaData/,/def badPlacesOver/,/def fieldOfModuli/]){
  for(const f of all){ const t=readFileSync(f,'utf8').split('\n'); for(let i=0;i<t.length;i++){ if(pat.test(t[i])){ console.log(f.replace(ROOT+'/tmp/sheaf/lana/','')+':'+(i+1)+': '+t[i].trim().slice(0,150)); } } }
}
