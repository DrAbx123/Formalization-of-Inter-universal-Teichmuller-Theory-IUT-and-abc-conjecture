import { readFileSync, existsSync, statSync, mkdirSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { dirname, join } from 'node:path';
import os from 'node:os';
const ROOT='D:/lean';
const TARGET='Pi1/FundamentalGroup/Galois.lean';
const hasOlean=(p)=>existsSync(join(ROOT,'.lake','build','lib','lean',p.replace(/\.lean$/,'')+'.olean'));
const info=(p)=>{ let t=''; try{t=readFileSync(join(ROOT,p),'utf8');}catch{return null;} const imps=[...t.matchAll(/^\s*(?:public\s+|private\s+|protected\s+)?import\s+([A-Za-z0-9_.]+)/gm)].map(m=>m[1]); const missing=[]; for(const im of imps){ if(/^(Mathlib|Lean|Init|Std|Batteries|Aesop|Qq|ProofWidgets|Plausible)/.test(im)) continue; const rel=im.replaceAll('.','/')+'.lean'; if(!hasOlean(rel)) missing.push(rel); } return missing; };
const closure=new Set(); const stack=[TARGET];
while(stack.length){ const p=stack.pop(); if(closure.has(p))continue; const m=info(p); if(m===null)continue; closure.add(p); for(const x of m) stack.push(x); }
console.log('closure size',closure.size);
const MAXT=420000; let compiled=0;
const runOne=(p)=>{ const free=os.freemem()/1024/1024; console.log('free MB',Math.round(free),'compile',p); if(free<4096){ console.log('LOW MEMORY, stopping'); return false; } const olean=join(ROOT,'.lake','build','lib','lean',p.replace(/\.lean$/,'')+'.olean'); mkdirSync(dirname(olean),{recursive:true}); const r=spawnSync('lake',['env','lean','-R',ROOT,'-o',olean,join(ROOT,p)],{cwd:ROOT,encoding:'utf8',timeout:MAXT,maxBuffer:64*1024*1024}); const ok=r.status===0 && existsSync(olean); if(!ok){ const err=(r.stderr||'')+(r.stdout||''); console.log('FAIL',p,'status',r.status,'exit',r.error?r.error.message:''); console.log(err.slice(-1500)); } else { console.log('DONE',p); compiled++; } return ok; };
let progress=true;
while(progress && !hasOlean(TARGET)){ progress=false; for(const p of closure){ if(hasOlean(p)) continue; const m=info(p); if(m===null) continue; if(m.every(x=>hasOlean(x))){ progress=true; const ok=runOne(p); if(!ok){ console.log('STOP at',p); process.exit(1); } } } }
console.log('compiled',compiled,'target olean',hasOlean(TARGET));
process.exit(hasOlean(TARGET)?0:2);