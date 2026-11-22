#!/usr/bin/env node
// Root lana Iut tree build (A880): Wall -> WallEquiv -> MainTheorem closure, root modules.
import fs from 'node:fs'; import path from 'node:path'; import { spawn } from 'node:child_process';
const ROOT=process.cwd(); const OUT=path.join(ROOT,'.lake/build/lib/lean');
const LOGDIR=path.join(ROOT,'tmp/iut_root/logs'); fs.mkdirSync(LOGDIR,{recursive:true});
const fileOf=m=>path.join(ROOT,m.split('.').join('/')+'.lean');
const oleanOf=m=>path.join(OUT,m.split('.').join('/')+'.olean');
const closure=fs.readFileSync(path.join(ROOT,'tmp/iut_root_closure.txt'),'utf8').split('\n').filter(Boolean);
const missingAll=fs.readFileSync(path.join(ROOT,'tmp/iut_root_missing.txt'),'utf8').split('\n').filter(Boolean);
const missing=missingAll.filter(m=>!m.startsWith('TemperedFundamentalGroups.')); const failedSet=new Set();
const closureSet=new Set(closure);
function importsOf(m){ const f=fileOf(m); if(!fs.existsSync(f)) return []; return fs.readFileSync(f,'utf8').split('\n').filter(l=>/^import /.test(l)).map(l=>l.replace(/^import /,'')); }
function rank(m){ if(/^Iut\.(Wall|WallEquiv)\./.test(m)||m==='Iut.MainTheorem') return 0; if(m.startsWith('Iut.')) return 1; if(m.startsWith('TemperedFundamentalGroups.')) return 2; return 3; }
function ready(m){ if(fs.existsSync(oleanOf(m))) return false; for(const im of importsOf(m)){ if(im.startsWith('Mathlib')||im.startsWith('Lean')) continue; if(!fs.existsSync(oleanOf(im))) return false; } return true; }
function compile(m){ return new Promise(res=>{ const f=fileOf(m), ole=oleanOf(m); fs.mkdirSync(path.dirname(ole),{recursive:true});
 const log=path.join(LOGDIR,m.replace(/[^A-Za-z0-9_]/g,'_')+'.log'); const out=fs.openSync(log,'w');
 const p=spawn('lake',['env','lean','-DmaxHeartbeats=2000000','-o',ole,f],{cwd:ROOT,stdio:['ignore',out,out]}); const t=setTimeout(()=>{try{p.kill('SIGKILL')}catch{}},1800000);
 p.on('close',code=>{clearTimeout(t); try{fs.closeSync(out)}catch{}; let first=''; try{const txt=fs.readFileSync(log,'utf8'); first=(txt.split('\n').find(l=>l.includes('error'))||'')}catch{}; res({m,code,ok:code===0&&fs.existsSync(ole),first});}); }); }
let fail=0; const results=[]; let builtCount=0; const start=Date.now();
while(true){
 const unbuilt=missing.filter(m=>!fs.existsSync(oleanOf(m)) && !failedSet.has(m));
 if(unbuilt.length===0) break;
 const readyList=unbuilt.filter(ready).sort((a,b)=>rank(a)-rank(b));
 if(readyList.length===0){ if(Date.now()-start>60*60*1000){ console.error('STOP wait'); break;} console.error('WAIT unbuilt='+unbuilt.length); await new Promise(r=>setTimeout(r,60000)); continue; }
 const batch=readyList.slice(0,6);
 const rs=await Promise.all(batch.map(compile));
 for(const r of rs){ if(!r.ok){ fail++; failedSet.add(r.m); results.push(r); console.error('FAIL '+r.m+' exit='+r.code+' '+(r.first||'').slice(0,200)); } else { builtCount++; } }
 const builtNow=missing.filter(m=>fs.existsSync(oleanOf(m))).length;
 fs.writeFileSync(path.join(ROOT,'tmp/iut_root/progress.json'), JSON.stringify({total:missing.length,built:builtNow,failed:fail,results:results.slice(-20)},null,2));
 if(builtCount%20 < 6) console.error('PROGRESS '+builtNow+'/'+missing.length);
}
const summary={total:missing.length,built:missing.filter(m=>fs.existsSync(oleanOf(m))).length,failed:fail};
fs.writeFileSync(path.join(ROOT,'tmp/iut_root/final.json'),JSON.stringify(summary,null,2));
console.log(JSON.stringify(summary,null,2));
