import { readFileSync, writeFileSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
const ROOT='D:/lean';
const dirs=process.argv.slice(2);
if(!dirs.length){ console.log('usage: node tools/transcode_lean_432.mjs <dir...>'); process.exit(1); }
function walk(d,out){ let e=[]; try{e=readdirSync(d,{withFileTypes:true})}catch{ return out; } for(const x of e){ if(x.name==='.lake'||x.name==='.git') continue; const p=join(d,x.name); if(x.isDirectory()) walk(p,out); else if(x.name.endsWith('.lean')) out.push(p); } return out; }
let files=0, changed=0; const samples=[];
for(const d of dirs){ for(const f of walk(join(ROOT,d),[])){ files++; let s=''; try{ s=readFileSync(f,'utf8'); }catch{ continue; } const before=s;
  s=s.replace(/^module\s*$/m,'');
  s=s.replace(/^public\s+import\s+/gm,'import ');
  s=s.replace(/^public\s+section\b/gm,'section');
  s=s.replace(/^public\s+(def|theorem|lemma|structure|class|instance|abbrev|inductive|noncomputable\s+def)\b/gm,'$1');
  s=s.replace(/^\s*public\s+(def|theorem|lemma|structure|class|instance|abbrev)\b/gm,(m,k)=>m.replace('public ',''));
  if(s!==before){ writeFileSync(f,s); changed++; if(samples.length<5) samples.push(f.replace(ROOT+'/','')); }
 } }
console.log(JSON.stringify({files,changed,samples},null,1));