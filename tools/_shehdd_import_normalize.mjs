import { readFileSync, writeFileSync, existsSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
const ROOT='D:/lean';
const FOUND='LeanFormal/IUT/Foundations/AlgebraicGeometry';
const files=[];
for(const d of ['LeanFormal/IUT/Foundations/AlgebraicGeometry','LeanFormal/IUT/IUTII/Kummer','LeanFormal/IUT/IUTII/Frobenioid']){
  try{ for(const f of readdirSync(join(ROOT,d))) if(f.endsWith('.lean')) files.push(d+'/'+f); }catch{}
}
let changed=0; const report=[];
for(const rel of files){
  const p=join(ROOT,rel);
  let txt; try{ txt=readFileSync(p,'utf8'); }catch{ continue; }
  let changedHere=false;
  const out=txt.split('\n').map(line=>{
    const m=line.match(/^import\s+(\S+)\s*$/); if(!m) return line;
    const imp=m[1]; if(imp.startsWith('Mathlib')||imp.startsWith('LeanFormal.IUT.Audit')) return line;
    const last=imp.split('.').pop();
    const oldPath=join(ROOT,imp.replaceAll('.','/')+'.lean');
    const newFile=join(ROOT,FOUND,last+'.lean');
    if(!existsSync(oldPath) && existsSync(newFile)){ changedHere=true; return 'import '+FOUND.replaceAll('/','.')+'.'+last; }
    return line;
  }).join('\n');
  if(changedHere){ writeFileSync(p,out); changed++; report.push(rel); }
}
console.log('files with import rewrites='+changed);
console.log(report.slice(0,20).join('\n'));
