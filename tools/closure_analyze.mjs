import { readFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const targets=process.argv.slice(2);
const hasOlean=(p)=>existsSync(ROOT+'/.lake/build/lib/lean/'+p.replace(/\.lean$/,'')+'.olean');
const cache=new Map();
const isMathlib=(m)=>/^(Mathlib|Lean|Init|Std|Batteries|Aesop|Qq|ProofWidgets|Plausible)/.test(m);
const deps=(p)=>{ if(cache.has(p))return cache.get(p); let t=''; try{t=readFileSync(ROOT+'/'+p,'utf8');}catch{cache.set(p,[]);return [];} const imps=[...t.matchAll(/^\s*(?:public\s+|private\s+|protected\s+)?import\s+([A-Za-z0-9_.]+)/gm)].map(m=>m[1]); const out=[]; for(const im of imps){ if(isMathlib(im)) continue; const rel=im.replaceAll('.','/')+'.lean'; if(existsSync(ROOT+'/'+rel)) out.push(rel); } cache.set(p,out); return out; };
for(const t of targets){ const seen=new Set(); const stack=[t]; while(stack.length){ const p=stack.pop(); if(seen.has(p))continue; seen.add(p); for(const d of deps(p)) stack.push(d); } const files=[...seen]; const missing=files.filter(p=>!hasOlean(p)); const tg=files.filter(p=>p.startsWith('TemperedFundamentalGroups/')); const pi1=files.filter(p=>p.startsWith('Pi1/')); const fsd=files.filter(p=>p.startsWith('FormalSchemes/')); console.log('TARGET '+t+' closure='+files.length+' missing='+missing.length+' TG='+tg.length+' Pi1='+pi1.length+' FS='+fsd.length); for(const x of tg.slice(0,8)) console.log('  TG '+x); }