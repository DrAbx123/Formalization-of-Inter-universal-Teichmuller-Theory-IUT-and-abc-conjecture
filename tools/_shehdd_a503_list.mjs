import { readFileSync, readdirSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const dirs=['tmp/external/Takkun-IUT_LEAN/IutLean','tmp/sheaf/takkun/IutLean'];
for(const d of dirs){
  const p=ROOT+'/'+d;
  console.log('DIR '+d+' exists='+existsSync(p));
  if(!existsSync(p)) continue;
  function walk(x,acc){ for(const e of readdirSync(x,{withFileTypes:true})){ const q=x+'/'+e.name; if(e.isDirectory()) walk(q,acc); else if(e.name.endsWith('.lean')) acc.push(q.replace(p+'/','')); } return acc; }
  const files=walk(p,[]);
  console.log('files='+files.length);
  console.log(files.slice(0,40).join('\n'));
  break;
}
