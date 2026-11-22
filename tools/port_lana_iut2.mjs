import { readFileSync, writeFileSync, readdirSync, existsSync, mkdirSync } from 'node:fs';
import { join, relative, dirname } from 'node:path';
const ROOT='D:/lean';
const LANA=join(ROOT,'tmp/dsh-oct6-openai-math-survey-20261016/repos/lana');
function walk(d,out){ let e=[]; try{e=readdirSync(d,{withFileTypes:true})}catch{ return out; } for(const x of e){ if(x.name==='.lake'||x.name==='.git') continue; const p=join(d,x.name); if(x.isDirectory()) walk(p,out); else if(x.name.endsWith('.lean')) out.push(p); } return out; }
const bases=[];
function findBases(d,depth){ if(depth>2) return; let e=[]; try{e=readdirSync(d,{withFileTypes:true})}catch{return} for(const x of e){ if(!x.isDirectory()) continue; const p=join(d,x.name); if(x.name==='.lake'||x.name==='.git') continue; if(existsSync(join(p,'lakefile.toml'))||existsSync(join(p,'lakefile.lean'))) bases.push(p); else findBases(p,depth+1); } }
findBases(LANA,0);
const mod2file=new Map(); const pkgOf=new Map();
for(const base of bases){ const short=relative(LANA,base).split(/[\\\/]/)[0]; const files=walk(base,[]); for(const f of files){ const rel=relative(base,f).replace(/\\/g,'/'); const mod=rel.replace(/\.lean$/,'').replace(/\//g,'.'); if(!mod2file.has(mod)){ mod2file.set(mod,f); pkgOf.set(mod,short); } } }
const portModOf=(m)=>'tmp.sheaf.lana.'+pkgOf.get(m)+'.'+m;
const importRe=/^\s*import\s+([A-Za-z0-9_.']+)/gm;
const iutBase=bases.find(b=>relative(LANA,b).split(/[\\\/]/)[0]==='iut');
const files=walk(iutBase,[]);
let n=0; const out=[];
for(const src of files){ const rel=relative(iutBase,src).replace(/\\/g,'/'); const dstRel='tmp/sheaf/lana/iut/'+rel; const dst=join(ROOT,dstRel); mkdirSync(dirname(dst),{recursive:true}); let s=readFileSync(src,'utf8'); s=s.replace(/^import\s+(?!Mathlib)([A-Za-z0-9_.']+)/gm,(line,mod)=>{ if(!mod2file.has(mod)) return line; return 'import '+portModOf(mod); }); writeFileSync(dst,s); out.push(dstRel); n++; }
writeFileSync(join(ROOT,'tmp','lana_iut_port_list.txt'), out.join('\n')+'\n');
console.log('re-ported iut files', n);