import { readFileSync, existsSync, writeFileSync } from 'node:fs';
const ROOT='D:/lean';
const files=readFileSync(ROOT+'/tmp/priority_files.txt','utf8').split(/\r?\n/).map(s=>s.trim()).filter(Boolean);
const set=new Set(files);
const cache=new Map();
const info=(p)=>{ if(cache.has(p))return cache.get(p); let t=''; try{t=readFileSync(ROOT+'/'+p,'utf8');}catch{cache.set(p,[]);return [];} const imps=[...t.matchAll(/^\s*(?:public\s+|private\s+|protected\s+)?import\s+([A-Za-z0-9_.]+)/gm)].map(m=>m[1]); const deps=[]; for(const im of imps){ if(/^(Mathlib|Lean|Init|Std|Batteries|Aesop|Qq|ProofWidgets|Plausible)/.test(im)) continue; const rel=im.replaceAll('.','/')+'.lean'; if(set.has(rel)) deps.push(rel); } cache.set(p,deps); return deps; };
const reachCache=new Map();
const reachesFS=(p)=>{ if(reachCache.has(p))return reachCache.get(p); if(p.startsWith('FormalSchemes/')){reachCache.set(p,true);return true;} const stack=[...info(p)]; const seen=new Set(); let res=false; while(stack.length){ const q=stack.pop(); if(seen.has(q))continue; seen.add(q); if(q.startsWith('FormalSchemes/')){res=true;break;} stack.push(...info(q)); } reachCache.set(p,res); return res; };
const a=[],b=[]; for(const f of files){ if(reachesFS(f)) b.push(f); else a.push(f); }
writeFileSync(ROOT+'/tmp/priority_a.txt',a.join('\n')+'\n','utf8');
writeFileSync(ROOT+'/tmp/priority_b.txt',b.join('\n')+'\n','utf8');
console.log('A='+a.length+' B='+b.length);