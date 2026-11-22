import { readFileSync, existsSync, mkdirSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { dirname, join } from 'node:path';
import os from 'node:os';
const ROOT='D:/lean';
const TARGET=process.argv[2];
if(!TARGET){ console.log('usage: node a836_chain.mjs <repo-relative-file>'); process.exit(9); }
const hasOlean=(p)=>existsSync(join(ROOT,'.lake','build','lib','lean',p.replace(/\.lean$/,'')+'.olean'));
const MOD=process.argv[3]||null;
const infoCache=new Map();
const info=(p)=>{ if(infoCache.has(p)) return infoCache.get(p); let t=''; try{t=readFileSync(join(ROOT,p),'utf8');}catch{infoCache.set(p,null);return null;} const imps=[...t.matchAll(/^\s*(?:public\s+|private\s+|protected\s+)?import\s+([A-Za-z0-9_.]+)/gm)].map(m=>m[1]); const missing=[]; for(const im of imps){ if(/^(Mathlib|Lean|Init|Std|Batteries|Aesop|Qq|ProofWidgets|Plausible)/.test(im)) continue; const rel=im.replaceAll('.','/')+'.lean'; if(!hasOlean(rel)) missing.push(rel); } const r={missing}; infoCache.set(p,r); return r; };
const closure=new Set(); const stack=[TARGET];
while(stack.length){ const p=stack.pop(); if(closure.has(p))continue; const m=info(p); if(m===null)continue; closure.add(p); for(const x of m.missing) stack.push(x); }
console.log('closure',closure.size);
const MAXT=420000; const runOne=(p)=>{ const free=os.freemem()/1024/1024; console.log('free MB',Math.round(free),'compile',p); if(free<4096){ console.log('LOW MEMORY'); return false; } const olean=join(ROOT,'.lake','build','lib','lean',p.replace(/\.lean$/,'')+'.olean'); mkdirSync(dirname(olean),{recursive:true}); const r=spawnSync('lake',['env','lean','-R',ROOT,'-o',olean,join(ROOT,p)],{cwd:ROOT,encoding:'utf8',timeout:MAXT,maxBuffer:32*1024*1024}); const ok=r.status===0&&existsSync(olean); if(!ok){ console.log('FAIL',p,'status',r.status); console.log(((r.stderr||'')+(r.stdout||'')).slice(-1500)); } else console.log('DONE',p); return ok; };
let progress=true;
while(progress && !hasOlean(TARGET)){ progress=false; for(const p of closure){ if(hasOlean(p))continue; const m=info(p); if(m===null)continue; if(m.missing.every(x=>hasOlean(x))){ progress=true; const ok=runOne(p); if(!ok){ console.log('STOP at',p); process.exit(1); } } } }
console.log('target olean',hasOlean(TARGET));
process.exit(hasOlean(TARGET)?0:2);