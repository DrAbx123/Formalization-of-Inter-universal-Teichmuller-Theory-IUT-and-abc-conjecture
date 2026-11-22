import { readFileSync, existsSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const dirs=['tmp/sheaf/xif/paper'];
function walk(x,acc){ for(const e of readdirSync(x,{withFileTypes:true})){ const p=x+'/'+e.name; if(e.isDirectory()) walk(p,acc); else if(e.name.endsWith('.lean')) acc.push(p); } return acc; }
const files=walk(ROOT+'/tmp/sheaf/xif/paper',[]);
for(const pat of [/def qPilotLogImage/,/def thetaPilotLogImage/,/def Cor312EpsilonArithmeticComparison/,/def qThetaStepXIContract/,/def step3115_comparison_proved/]){
  for(const f of files){ const t=readFileSync(f,'utf8').split('\n'); for(let i=0;i<t.length;i++){ if(pat.test(t[i])){ console.log(f.replace(ROOT+'/','')+':'+(i+1)); const j0=i, j1=Math.min(t.length,i+22); console.log(t.slice(j0,j1).map((x,k)=>(j0+k+1)+': '+x).join('\n')); console.log('---'); } } }
}
