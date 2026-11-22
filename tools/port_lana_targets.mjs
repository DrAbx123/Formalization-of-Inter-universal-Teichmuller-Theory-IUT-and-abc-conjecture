
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
const importRe=/^\s*import\s+([A-Za-z0-9_.']+)/gm;
const args=process.argv.slice(2);
let DSTPREFIX='tmp/sheaf/lana/'; const rest=[];
for(const a of args){ if(a.startsWith('--dst=')){ DSTPREFIX=a.slice(6).replace(/\/$/,'')+'/'; } else rest.push(a); }
const targets=rest;
if(!targets.length){ console.error('usage: node tools/port_lana_targets.mjs Iut.Module1 Iut.Module2 ...'); process.exit(1); }
// mechanical fix rules
const rules=[];
for(const rf of ['port_fix_rules.txt','port_rename_map.txt']) {
  const p=join(ROOT,'tools',rf); if(!existsSync(p)) continue;
  for(const line of readFileSync(p,'utf8').split(/\r?\n/)) {
    const t=line.trim(); if(!t||t.startsWith('#')) continue;
    const parts=t.split('||'); if(parts.length!==2) continue;
    try { rules.push([new RegExp(parts[0].trim(),'g'), parts[1].trim()]); } catch(e) {}
  }
}
const applyFixes=(s)=>{ for(const [re,rep] of rules) s=s.replace(re,rep); return s; };
const seen=new Set(); const stack=[...targets];
while(stack.length){ const m=stack.pop(); if(seen.has(m)) continue; seen.add(m); const f=mod2file.get(m); if(!f){ console.error('MISSING module',m); continue; } let s=''; try{ s=readFileSync(f,'utf8'); }catch{ continue; } let mm; importRe.lastIndex=0; while((mm=importRe.exec(s))){ const im=mm[1]; if(im.startsWith('Mathlib')) continue; if(!mod2file.has(im)) continue; if(!seen.has(im)) stack.push(im); } }
const modPrefix=DSTPREFIX.replace(/\//g,'.'); const portModOf=(m)=>modPrefix+pkgOf.get(m)+'.'+m;
const out=[];
for(const m of seen){ const src=mod2file.get(m); const short=pkgOf.get(m); const base=bases.find(b=>relative(LANA,b).split(/[\\\/]/)[0]===short); const rel=relative(base,src).replace(/\\/g,'/'); const dstRel=DSTPREFIX+short+'/'+rel; const dst=join(ROOT,dstRel); mkdirSync(dirname(dst),{recursive:true}); let s=applyFixes(readFileSync(src,'utf8')); s=s.replace(/^import\s+(?!Mathlib)([A-Za-z0-9_.']+)/gm,(line,mod)=>{ if(!mod2file.has(mod)) return line; return 'import '+portModOf(mod); }); writeFileSync(dst,s); out.push(dstRel+'  ['+m+']'); }
const listName='tools/_port_list_'+targets.join('_').replace(/[^A-Za-z0-9]/g,'_')+'.txt';
writeFileSync(join(ROOT,listName), out.join('\n')+'\n');
console.log('ported', out.length, 'files; list:', listName);
console.log(out.join('\n'));
