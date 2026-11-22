import { readdirSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const d=ROOT+'/tmp/dsh-oct6-openai-math-survey-20261016/repos/lana/iut/iut-main/Iut4Sec1';
function walk(x,acc){ for(const e of readdirSync(x,{withFileTypes:true})){ const p=x+'/'+e.name; if(e.isDirectory()) walk(p,acc); else if(e.name.endsWith('.lean')) acc.push(p.replace(d+'/','')); } return acc; }
console.log(walk(d,[]).join('\n'));
