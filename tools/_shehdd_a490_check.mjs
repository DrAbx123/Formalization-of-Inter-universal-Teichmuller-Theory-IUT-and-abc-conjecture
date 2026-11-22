import { existsSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const portedIut=ROOT+'/tmp/sheaf/lana/iut';
console.log('ported iut exists='+existsSync(portedIut));
if(existsSync(portedIut)){ const walk=(d,acc)=>{ for(const e of readdirSync(d,{withFileTypes:true})){ const p=d+'/'+e.name; if(e.isDirectory()) walk(p,acc); else if(e.name.endsWith('.lean')) acc.push(p); } return acc; }; const files=walk(portedIut,[]); console.log('ported iut files='+files.length); console.log('Wall files: '+files.filter(f=>f.includes('/Wall/')).length); }
console.log('orig Checks exists='+existsSync(ROOT+'/tmp/dsh-oct6-openai-math-survey-20261016/repos/lana/iut/iut-main/Iut/Wall/Checks.lean'));
