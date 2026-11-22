import { readFileSync, existsSync, mkdirSync, statSync } from 'node:fs';
import { join, dirname, relative } from 'node:path';
import { spawnSync } from 'node:child_process';
const ROOT='D:/lean';
const FOUND='LeanFormal/IUT/Foundations/AlgebraicGeometry';
const targets=['SourcePsiMinimalModelUniqueness','SourcePsiActualMinimalModelReduction','SourcePsiCorrectedReductionSpecialFiber','SourcePsiIntegralModelReduction','SourcePsiReductionActualConstruct','SourcePsiReductionTypeActual','SourcePsiStableReductionFinal','SourcePsiStableReductionFinalConsumer','SourcePsiStableReductionFromSource','SourcePsiIntegralModel','SourcePsiActualMinimalModelInhabited','SourcePsiActualMinimality'];
const fileForModule=(mod)=>{
  const direct=ROOT+'/'+mod.replaceAll('.','/')+'.lean';
  if(existsSync(direct)) return direct;
  const m=mod.split('.').pop();
  const cands=[ROOT+'/'+FOUND+'/'+m+'.lean'];
  for(const c of cands){ if(existsSync(c)) return c; }
  return null;
};
const compiled=new Map(); const failed=[];
const compile=(file, stack=[])=>{
  if(compiled.has(file)) return compiled.get(file);
  if(stack.includes(file)){ compiled.set(file,true); return true; }
  const rel=file.replace(ROOT+'/','');
  const ole=ROOT+'/'+'.lake/build/lib/lean/'+rel.replace(/\.lean$/,'.olean');
  mkdirSync(dirname(ole),{recursive:true});
  const src=readFileSync(file,'utf8');
  const imports=[...src.matchAll(/^import\s+(\S+)/gm)].map(m=>m[1]);
  for(const imp of imports){
    if(imp.startsWith('Mathlib')) continue;
    const dep=fileForModule(imp);
    if(dep){ if(!compile(dep,[...stack,file])){ compiled.set(file,false); return false; } }
  }
  // skip if olean fresh
  if(existsSync(ole) && statSync(ole).mtimeMs>=statSync(file).mtimeMs){ compiled.set(file,true); return true; }
  const r=spawnSync('lake',['env','lean','-R','.','-o',ole,rel],{cwd:ROOT,encoding:'utf8',maxBuffer:1024*1024*32});
  if(r.status===0 && existsSync(ole)){ compiled.set(file,true); return true; }
  const err=(r.stderr||'').split('\n').filter(l=>l.includes(': error')).slice(0,2);
  failed.push({rel,err});
  compiled.set(file,false);
  return false;
};
for(const t of targets){ const f=ROOT+'/'+FOUND+'/'+t+'.lean'; if(existsSync(f)) compile(f); }
console.log('compiled='+ [...compiled.entries()].filter(([k,v])=>v).length + ' failed='+failed.length);
for(const f of failed.slice(0,15)) console.log('FAIL '+f.rel+' :: '+f.err.join(' || '));
