
import { readFileSync, writeFileSync, readdirSync, existsSync, mkdirSync, copyFileSync } from 'node:fs';
import { join, relative, dirname } from 'node:path';
const ROOT='D:/lean';
const SRC=join(ROOT,'tmp/online/lana-agents__iut/iut-main');
const DST=join(ROOT,'tmp/external/ported/lana_tgfree');
function walk(d,out){ let e=[]; try{e=readdirSync(d,{withFileTypes:true})}catch{return out;} for(const x of e){ if(x.name==='.lake'||x.name==='.git') continue; const p=join(d,x.name); if(x.isDirectory()) walk(p,out); else if(x.name.endsWith('.lean')) out.push(p); } return out; }
const files=walk(SRC,[]);
const mod2file=new Map();
for(const f of files){ const rel=relative(SRC,f).replace(/\\/g,'/'); const mod=rel.replace(/\.lean$/,'').replace(/\//g,'.'); mod2file.set(mod,f); }
const importRe=/^\s*import\s+([A-Za-z0-9_.']+)/gm;
const targets=['Iut.WallEquiv.Gap','Iut.WallEquiv.VcI','Iut.Concrete.ThetaRegion','Iut.Concrete.LocalTheory'];
const seen=new Set(); const stack=[...targets]; const missing=new Set();
while(stack.length){ const m=stack.pop(); if(seen.has(m)) continue; seen.add(m); const f=mod2file.get(m); if(!f){ missing.add(m); continue; } const s=readFileSync(f,'utf8'); let mm; importRe.lastIndex=0; while((mm=importRe.exec(s))){ const im=mm[1]; if(im.startsWith('Mathlib')||im.startsWith('Lean')||im.startsWith('Std')) continue; if(mod2file.has(im)){ if(!seen.has(im)) stack.push(im); } else missing.add(im); } }
console.log('closure',seen.size,'missing',missing.size); console.log([...missing].slice(0,30).join('\n'));
const PREFIX='tmp.external.ported.lana_tgfree.';
const filesToCopy=[]; const relOf=new Map();
for(const m of seen){ const f=mod2file.get(m); if(!f) continue; const rel=relative(SRC,f).replace(/\\/g,'/'); relOf.set(m,rel); }
for(const m of seen){ const f=mod2file.get(m); if(!f) continue; let s=readFileSync(f,'utf8'); s=s.replace(/^(\s*)import\s+(Iut[.0-9A-Za-z_']*)/gm,(line,ind,mod)=>{ if(seen.has(mod)) return ind+'import '+PREFIX+mod; return line; }); s='/- Ported from '+relative(SRC,f).replace(/\\/g,'/')+' (lana TG-free). Imports rewritten; mathematical content unchanged. -/\n'+s; const rel=relOf.get(m); const dst=join(DST,rel); mkdirSync(dirname(dst),{recursive:true}); writeFileSync(dst,s); filesToCopy.push(rel); }
// waves: level = 1 + max(level of local imports)
const levelOf=new Map(); const levels=new Map();
function level(m,visiting){ if(levelOf.has(m)) return levelOf.get(m); if(visiting.has(m)) return 0; visiting.add(m); const f=mod2file.get(m); if(!f){ levelOf.set(m,0); return 0; } const s=readFileSync(f,'utf8'); let mm; importRe.lastIndex=0; let l=0; while((mm=importRe.exec(s))){ const im=mm[1]; if(seen.has(im)&&im!==m) l=Math.max(l,level(im,visiting)); } const res=l+1; levelOf.set(m,res); return res; }
for(const m of seen) level(m,new Set());
for(const m of seen){ const lv=levelOf.get(m); if(!levels.has(lv)) levels.set(lv,[]); levels.get(lv).push('tmp/external/ported/lana_tgfree/'+relOf.get(m)); }
const waves=[]; const ks=[...levels.keys()].sort((a,b)=>a-b); for(const k of ks) waves.push(levels.get(k).sort());
writeFileSync(join(ROOT,'tmp/lana_tgfree_waves.json'),JSON.stringify({created:new Date().toISOString(),waves},null,1));
console.log('waves',waves.map(w=>w.length).join(','));
writeFileSync(join(DST,'PORT-INFO.json'),JSON.stringify({targets,closure:seen.size,missing:[...missing],waves:waves.map(w=>w.length)},null,1));
