import { readFileSync, existsSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
function walk(x,acc){ for(const e of readdirSync(x,{withFileTypes:true})){ const p=x+'/'+e.name; if(e.isDirectory()){ if(['.lake','.git','logs'].includes(e.name)) continue; walk(p,acc); } else if(e.name.endsWith('.lean')) acc.push(p); } return acc; }
const files=walk(ROOT+'/tmp/sheaf/xif/paper',[]).concat(walk(ROOT+'/LeanFormal',[]));
for(const pat of [/def Cor312EpsilonArithmeticComparison/,/def SHEArrowStatement/,/theorem sheArrowStatement_proved/,/def qVFamily/,/def localSignedLog/,/def r4_endgame_composition/,/theorem r4_endgame_composition/]){
  let done=false;
  for(const f of files){ if(done) break; const t=readFileSync(f,'utf8').split('\n'); for(let i=0;i<t.length;i++){ if(pat.test(t[i])){ console.log(f.replace(ROOT+'/','')+':'+(i+1)); console.log(t.slice(i,Math.min(t.length,i+18)).map((x,k)=>(i+k+1)+': '+x).join('\n')); console.log('---'); done=true; break; } } }
}
