import { readFileSync, existsSync, mkdirSync, readdirSync, statSync } from 'node:fs';
import { spawn } from 'node:child_process';
import { dirname, join } from 'node:path';
import os from 'node:os';
const ROOT='D:/lean';
const PREFIX=process.argv[2];
const N=Number(process.argv[3]||8);
if(!PREFIX){ console.log('usage: node vendor_port.mjs <prefix> [n]'); process.exit(9); }
const walk=(d,out)=>{ for(const e of readdirSync(join(ROOT,d),{withFileTypes:true})){ if(e.name.startsWith('.'))continue; const p=d+'/'+e.name; if(e.isDirectory()) walk(p,out); else if(e.name.endsWith('.lean')) out.push(p); } };
const files=[]; walk(PREFIX,files);
const hasOlean=(p)=>existsSync(join(ROOT,'.lake','build','lib','lean',p.replace(/\.lean$/,'')+'.olean'));
const cache=new Map();
const info=(p)=>{ if(cache.has(p)) return cache.get(p); let t=''; try{t=readFileSync(join(ROOT,p),'utf8');}catch{cache.set(p,[]);return [];} const imps=[...t.matchAll(/^\s*(?:public\s+|private\s+|protected\s+)?import\s+([A-Za-z0-9_.]+)/gm)].map(m=>m[1]); const missing=[]; for(const im of imps){ if(/^(Mathlib|Lean|Init|Std|Batteries|Aesop|Qq|ProofWidgets|Plausible)/.test(im)) continue; const rel=im.replaceAll('.','/')+'.lean'; if(existsSync(join(ROOT,rel)) && !hasOlean(rel)) missing.push(rel); } cache.set(p,missing); return missing; };
const fails=new Map(); const errs=[];
const runOne=(p)=>new Promise((resolve)=>{ const free=os.freemem()/1024/1024; if(free<3500){ console.log('LOWMEM'); resolve(false); return; } const olean=join(ROOT,'.lake','build','lib','lean',p.replace(/\.lean$/,'')+'.olean'); mkdirSync(dirname(olean),{recursive:true}); const ch=spawn('lake',['env','lean','-R',ROOT,'-o',olean,join(ROOT,p)],{cwd:ROOT,windowsHide:true}); let out=''; ch.stdout.on('data',d=>{out+=d;}); ch.stderr.on('data',d=>{out+=d;}); ch.on('close',(code)=>{ const ok=code===0&&existsSync(olean); if(!ok){ fails.set(p,code); const first=(out.split('\n').find(l=>l.includes(': error'))||out.split('\n')[0]||'').slice(0,220); errs.push(p+' :: '+first); } else console.log('DONE '+p); resolve(ok); }); });
const main=async()=>{ let progress=true; let round=0; while(progress){ round++; progress=false; const missing=files.filter(p=>!hasOlean(p)&&!fails.has(p)); const ready=missing.filter(p=>info(p).every(x=>hasOlean(x)||fails.has(x))); if(ready.length===0) break; for(let i=0;i<ready.length;i+=N){ const batch=ready.slice(i,i+N); const res=await Promise.all(batch.map(runOne)); if(res.some(x=>x)) progress=true; } }; const done=files.filter(hasOlean).length; console.log('SUMMARY '+PREFIX+' compiled='+done+'/'+files.length+' fails='+fails.size); const grouped=new Map(); for(const e of errs){ const key=e.split(' :: ')[1]||e; grouped.set(key,(grouped.get(key)||0)+1); } console.log('TOP_ERRORS'); for(const [k,v] of [...grouped.entries()].sort((a,b)=>b[1]-a[1]).slice(0,5)) console.log(' x'+v+' '+k); for(const e of errs.slice(0,12)) console.log('FAIL '+e); };
main();