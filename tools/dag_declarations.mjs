import { readdirSync, readFileSync, writeFileSync, statSync } from 'node:fs';
import { join, relative } from 'node:path';
const ROOT='D:/lean'; const OUT=join(ROOT,'dag','generated');
const skipDirs=new Set(['.lake','.git','node_modules','.dsh']);
const files=[];
function walk(dir){ let es; try{es=readdirSync(dir,{withFileTypes:true});}catch{return;} for(const e of es){ if(e.name.startsWith('.')||skipDirs.has(e.name))continue; const p=join(dir,e.name); if(e.isDirectory())walk(p); else if(e.isFile()&&e.name.endsWith('.lean'))files.push(p); } }
walk(ROOT);
const rel=(p)=>relative(ROOT,p).replaceAll('\\','/');
const kw=/(?:^|\n)\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*(theorem|lemma|def|abbrev|structure|class|inductive|instance)\s+([A-Za-z_\u00C0-\uFFFF][A-Za-z0-9_'!?\u2080-\u209f\u00C0-\uFFFF.]*)/g;
const decls=[];
for(const p of files){ let src=''; try{src=readFileSync(p,'utf8');}catch{continue;} if(!/(theorem|lemma|def|abbrev|structure|class|inductive|instance)\s/.test(src)) continue;
  const r=rel(p); let m; kw.lastIndex=0;
  while((m=kw.exec(src))!==null){ decls.push({ name:m[2], kind:m[1], file:r, line:src.slice(0,m.index).split('\n').length }); }
}
writeFileSync(join(OUT,'declarations-index.json'), JSON.stringify({ root:ROOT, declaration_count:decls.length, declarations:decls }));
console.log(JSON.stringify({ files:files.length, declarations:decls.length },null,2));