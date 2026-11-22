import { readFileSync, writeFileSync, existsSync, openSync, closeSync, unlinkSync, renameSync, readdirSync } from 'node:fs';
import { join, relative } from 'node:path';
const ROOT='D:/lean'; const ET=join(ROOT,'dag/watchdog/extra-targets.txt'); const LOCK=join(ROOT,'dag/watchdog','.extras.lock');
const targets=process.argv.slice(2).flatMap(a=>a.includes('*')?[]:[a]).filter(Boolean);
if(!targets.length){ console.log('usage: node tools/extras_add_closure.mjs <lean files...>'); process.exit(1); }
// build module -> file map for whole repo (exclude .lake/.git)
function walk(d,out){ let e=[]; try{e=readdirSync(d,{withFileTypes:true})}catch{ return out; } for(const x of e){ if(x.name==='.lake'||x.name==='.git'||x.name==='.lean-shadow'||x.name==='node_modules') continue; const p=join(d,x.name); if(x.isDirectory()) walk(p,out); else if(x.name.endsWith('.lean')) out.push(p); } return out; }
const all=walk(ROOT,[]); const mod2file=new Map();
for(const f of all){ const mod=relative(ROOT,f).replace(/\\/g,'/').replace(/\.lean$/,'').replace(/\//g,'.'); if(!mod2file.has(mod)) mod2file.set(mod,f); }
const importRe=/^\s*(?:public\s+)?import\s+([A-Za-z0-9_.']+)/gm;
const seen=new Set(); const stack=[];
for(const t of targets){ const abs=join(ROOT,t); if(!existsSync(abs)){ console.log('missing target '+t); continue; } stack.push(abs); }
while(stack.length){ const f=stack.pop(); if(seen.has(f)) continue; seen.add(f); let s=''; try{ s=readFileSync(f,'utf8'); }catch{ continue; } let m; while((m=importRe.exec(s))){ const dep=mod2file.get(m[1]); if(dep && !seen.has(dep)) stack.push(dep); } }
let fd=null; for(let i=0;i<240;i++){ try{ fd=openSync(LOCK,'wx'); break; }catch{ await new Promise(r=>setTimeout(r,250)); } }
const raw=readFileSync(ET,'utf8').split(/\r?\n/).filter(Boolean); const set=new Set(raw); let added=0;
const rel=[...seen].map(f=>relative(ROOT,f).replace(/\\/g,'/'));
for(const p of rel){ if(!set.has(p)){ set.add(p); raw.push(p); added++; } }
const tmp=ET+'.tmp'; writeFileSync(tmp, raw.join('\n')+'\n'); renameSync(tmp,ET);
if(fd!==null){ try{ closeSync(fd); }catch{} try{ unlinkSync(LOCK); }catch{} }
console.log(JSON.stringify({closure:rel.length,added,total:raw.length},null,1));