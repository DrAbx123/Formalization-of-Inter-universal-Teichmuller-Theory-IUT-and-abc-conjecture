import { readFileSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
function walk(x,acc){ for(const e of readdirSync(x,{withFileTypes:true})){ const p=x+'/'+e.name; if(e.isDirectory()) walk(p,acc); else if(e.name.endsWith('.lean')) acc.push(p); } return acc; }
const files=walk(ROOT+'/tmp/sheaf/xif/paper',[]);
for(const pat of [/theorem she_arrow_apply/,/def rootNormedElement/,/def qPilotCompletionImage/,/theorem rootExtensionProductThetaImage_oneThetaLabel/]){
  for(const f of files){ const t=readFileSync(f,'utf8').split('\n'); for(let i=0;i<t.length;i++){ if(pat.test(t[i])){ console.log(f.replace(ROOT+'/','')+':'+(i+1)); console.log(t.slice(i,Math.min(t.length,i+16)).map((x,k)=>(i+k+1)+': '+x).join('\n')); console.log('---'); } } }
}
