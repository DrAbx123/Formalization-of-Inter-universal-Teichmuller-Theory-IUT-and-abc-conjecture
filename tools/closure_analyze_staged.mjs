import { readFileSync, existsSync } from 'node:fs';
import { join } from 'node:path';
const ROOT=process.argv[2]; const targets=process.argv.slice(3);
const hasOlean=(p)=>existsSync(join(ROOT,'.lake/build/lib/lean',p.replace(/\.lean$/,'')+'.olean'));
const cache=new Map();
const isMathlib=(m)=>/^(Mathlib|Lean|Init|Std|Batteries|Aesop|Qq|ProofWidgets|Plausible)/.test(m);
const deps=(p)=>{ if(cache.has(p))return cache.get(p); let t=''; try{t=readFileSync(join(ROOT,p),'utf8');}catch{cache.set(p,[]);return [];} const imps=[...t.matchAll(/^\s*(?:public\s+|private\s+|protected\s+)?import\s+([A-Za-z0-9_.]+)/gm)].map(m=>m[1]); const out=[]; for(const im of imps){ if(isMathlib(im))continue; const rel=im.replaceAll('.','/')+'.lean'; if(existsSync(join(ROOT,rel))) out.push(rel); } cache.set(p,out); return out; };
const forbid=(p)=>/Cor312\/Statement|Cor312\/ThetaData|Anabelian\/Tempered|Anabelian\/Genuine\/GenuineEtale|TemperedFundamentalGroups\//.test(p);
for(const t of targets){ const seen=new Set(); const stack=[t]; while(stack.length){ const p=stack.pop(); if(seen.has(p))continue; if(!existsSync(join(ROOT,p)))continue; seen.add(p); for(const d of deps(p)) stack.push(d); } const files=[...seen]; const bad=files.filter(forbid); console.log('TARGET '+t+' closure='+files.length+' forbidden='+bad.length); for(const b of bad.slice(0,10)) console.log('  FORBIDDEN '+b); }