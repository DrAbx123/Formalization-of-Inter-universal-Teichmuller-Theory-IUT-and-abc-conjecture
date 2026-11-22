import { readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join, relative } from 'node:path';
const ROOT='D:/lean';
function walk(d,out){ let e=[]; try{e=readdirSync(d,{withFileTypes:true})}catch{ return out; } for(const x of e){ if(x.name==='.lake'||x.name==='.git') continue; const p=join(d,x.name); if(x.isDirectory()) walk(p,out); else if(x.name.endsWith('.lean')) out.push(p); } return out; }
const rel=(f,b)=>relative(b,f).replace(/\\/g,'/');
// our mathlib decl names
const ourDir=join(ROOT,'.lake/packages/mathlib/Mathlib');
const ourFiles=walk(ourDir,[]);
const declRe=/^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+|scoped\s+|local\s+)*(?:theorem|lemma|def|abbrev|structure|class|inductive|instance)\s+([A-Za-z_][A-Za-z0-9_.']*)/;
const ourNames=new Set(); const ourFileSet=new Set();
for(const f of ourFiles){ ourFileSet.add(rel(f,join(ROOT,'.lake/packages/mathlib'))); let s=''; try{ s=readFileSync(f,'utf8'); }catch{ continue; } for(const line of s.split(/\r?\n/)){ const m=declRe.exec(line); if(m) ourNames.add(m[1]); } }
console.log('our decls',ourNames.size);
// 4.36 new files
const newDir=join(ROOT,'tmp/mathlib4-4.36.0-rc2/Mathlib');
const newFiles=walk(newDir,[]);
const out=[];
for(const f of newFiles){ const r=rel(f,join(ROOT,'tmp/mathlib4-4.36.0-rc2')); if(ourFileSet.has(r)) continue; let s=''; try{ s=readFileSync(f,'utf8'); }catch{ continue; } const names=[]; for(const line of s.split(/\r?\n/)){ const m=declRe.exec(line); if(m && !ourNames.has(m[1])) names.push(m[1]); } if(names.length){ out.push({file:r,newCount:names.length,names:names.slice(0,12)}); } }
out.sort((a,b)=>b.newCount-a.newCount);
console.log('new files with genuinely new decl names',out.length);
writeFileSync(join(ROOT,'tmp/mathlib436_new_decls.json'),JSON.stringify(out,null,1));
for(const o of out.slice(0,60)) console.log(o.newCount+' '+o.file+' :: '+o.names.slice(0,5).join(', '));