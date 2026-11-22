import { spawnSync } from 'node:child_process';
import { existsSync, mkdirSync, readFileSync, appendFileSync, readdirSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { spawn } from 'node:child_process';
import os from 'node:os';
const ROOT='D:/lean';
const LIST=join(ROOT,'tmp','back_queue.txt');
const N=Number(process.env.BACK_N||2);
let files=[]; try{ files=readFileSync(LIST,'utf8').split(/\r?\n/).map(s=>s.trim()).filter(Boolean); }catch{ console.log('back queue list missing'); process.exit(0); }
const hasOlean=(p)=>existsSync(join(ROOT,'.lake','build','lib','lean',p.replace(/\.lean$/,'')+'.olean'));
const infoCache=new Map();
const info=(p)=>{ if(infoCache.has(p)) return infoCache.get(p); let t=''; try{t=readFileSync(join(ROOT,p),'utf8');}catch{infoCache.set(p,[]);return [];} const imps=[...t.matchAll(/^\s*(?:public\s+|private\s+|protected\s+)?import\s+([A-Za-z0-9_.]+)/gm)].map(m=>m[1]); const missing=[]; for(const im of imps){ if(/^(Mathlib|Lean|Init|Std|Batteries|Aesop|Qq|ProofWidgets|Plausible)/.test(im)) continue; const rel=im.replaceAll('.','/')+'.lean'; if(existsSync(join(ROOT,rel))&&!hasOlean(rel)) missing.push(rel); } infoCache.set(p,missing); return missing; };
const fails=new Map(); const errs=[];
const runOne=(p)=>new Promise((resolve)=>{ if(os.freemem()/1024/1024<3500){ resolve(false); return; } const olean=join(ROOT,'.lake','build','lib','lean',p.replace(/\.lean$/,'')+'.olean'); mkdirSync(dirname(olean),{recursive:true}); const ch=spawn('lake',['env','lean','-R',ROOT,'-o',olean,join(ROOT,p)],{cwd:ROOT,windowsHide:true}); let out=''; ch.stdout.on('data',d=>out+=d); ch.stderr.on('data',d=>out+=d); ch.on('close',(code)=>{ const ok=code===0&&existsSync(olean); if(!ok){ fails.set(p,code); const first=(out.split('\n').find(l=>l.includes(': error'))||'').trim().slice(0,260); errs.push(p+' | '+code+' | '+first); } else console.log('DONE '+p); resolve(ok); }); });
const main=async()=>{ let progress=true; while(progress){ progress=false; const missing=files.filter(p=>!hasOlean(p)&&!fails.has(p)); const ready=missing.filter(p=>info(p).every(x=>hasOlean(x))); if(!ready.length) break; for(let i=0;i<ready.length;i+=N){ const res=await Promise.all(ready.slice(i,i+N).map(runOne)); if(res.some(x=>x)) progress=true; } } const done=files.filter(hasOlean).length; appendFileSync(join(ROOT,'tmp','back_queue_results.csv'),errs.map(e=>e.replaceAll('\n',' ')).join('\n')+(errs.length?'\n':''),'utf8'); console.log('SUMMARY back compiled='+done+'/'+files.length+' fails='+fails.size); for(const e of errs.slice(0,10)) console.log('FAIL '+e); };
main();