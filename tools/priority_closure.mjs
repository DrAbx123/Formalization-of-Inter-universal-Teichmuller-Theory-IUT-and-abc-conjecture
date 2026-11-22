import { readFileSync, existsSync, writeFileSync } from 'node:fs';
const ROOT='D:/lean';
const targets=process.argv.slice(2);
const hasOlean=(p)=>existsSync(ROOT+'/.lake/build/lib/lean/'+p.replace(/\.lean$/,'')+'.olean');
const cache=new Map();
const info=(p)=>{ if(cache.has(p)) return cache.get(p); let t=''; try{t=readFileSync(ROOT+'/'+p,'utf8');}catch{cache.set(p,[]);return [];} const imps=[...t.matchAll(/^\s*(?:public\s+|private\s+|protected\s+)?import\s+([A-Za-z0-9_.]+)/gm)].map(m=>m[1]); const miss=[]; for(const im of imps){ if(/^(Mathlib|Lean|Init|Std|Batteries|Aesop|Qq|ProofWidgets|Plausible)/.test(im)) continue; const rel=im.replaceAll('.','/')+'.lean'; if(existsSync(ROOT+'/'+rel)&&!hasOlean(rel)) miss.push(rel); } cache.set(p,miss); return miss; };
const closure=new Set(); const stack=[...targets];
while(stack.length){ const p=stack.pop(); if(closure.has(p))continue; const m=info(p); closure.add(p); for(const x of m) stack.push(x); }
const missing=[...closure].filter(p=>!hasOlean(p));
writeFileSync(ROOT+'/tmp/priority_files.txt',missing.join('\n')+'\n','utf8');
console.log('closure='+closure.size+' missing='+missing.length);