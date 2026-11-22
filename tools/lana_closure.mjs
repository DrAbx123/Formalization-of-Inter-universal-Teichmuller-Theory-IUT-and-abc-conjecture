import { readFileSync, readdirSync, existsSync, statSync } from 'node:fs';
import { join, relative } from 'node:path';
const ROOT='D:/lean';
const LANA=join(ROOT,'tmp/dsh-oct6-openai-math-survey-20261016/repos/lana');
function walk(d,out,skip){ let e=[]; try{e=readdirSync(d,{withFileTypes:true})}catch{ return out; } for(const x of e){ if(x.name==='.lake'||x.name==='.git') continue; const p=join(d,x.name); if(x.isDirectory()){ if(skip && skip(p)) continue; walk(p,out,skip); } else if(x.name.endsWith('.lean')) out.push(p); } return out; }
const bases=[];
function findBases(d,depth){ if(depth>2) return; let e=[]; try{e=readdirSync(d,{withFileTypes:true})}catch{return} for(const x of e){ if(!x.isDirectory()) continue; const p=join(d,x.name); if(x.name==='.lake'||x.name==='.git') continue; if(existsSync(join(p,'lakefile.toml'))||existsSync(join(p,'lakefile.lean'))) bases.push(p); else findBases(p,depth+1); } }
findBases(LANA,0);
console.log('bases',bases.length);
const mod2file=new Map(); const pkgOf=new Map();
for(const base of bases){ const files=walk(base,[],null); for(const f of files){ const rel=relative(base,f).replace(/\\/g,'/'); const mod=rel.replace(/\.lean$/,'').replace(/\//g,'.'); if(!mod2file.has(mod)){ mod2file.set(mod,f); pkgOf.set(mod,relative(LANA,base).replace(/\\/g,'/')); } } }
const importRe=/^\s*import\s+([A-Za-z0-9_.']+)/gm;
const targetMod='Iut.MainTheorem';
console.log('target exists', mod2file.has(targetMod));
const seen=new Set(); const stack=[targetMod]; const missing=new Set();
while(stack.length){ const m=stack.pop(); if(seen.has(m)) continue; seen.add(m); const f=mod2file.get(m); if(!f) continue; let s=''; try{ s=readFileSync(f,'utf8'); }catch{ continue; } let mm; while((mm=importRe.exec(s))){ const im=mm[1]; if(im.startsWith('Mathlib')) continue; if(!mod2file.has(im)){ missing.add(im); continue; } if(!seen.has(im)) stack.push(im); } }
const byPkg={}; for(const m of seen){ const p=pkgOf.get(m)||'?'; byPkg[p]=(byPkg[p]||0)+1; }
console.log('closure modules', seen.size);
console.log(JSON.stringify(Object.entries(byPkg).sort((a,b)=>b[1]-a[1]),null,1));
console.log('missing modules', missing.size, [...missing].slice(0,25));