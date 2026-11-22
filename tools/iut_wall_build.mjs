#!/usr/bin/env node
// Build lana Iut Wall/WallEquiv/Concrete/LogLink/MainTheorem chain with wave-parallel single-file lean.
import fs from 'node:fs';
import path from 'node:path';
import { spawn } from 'node:child_process';
const ROOT = process.cwd();
const OUT = path.join(ROOT, '.lake/build/lib/lean');
const LOGDIR = path.join(ROOT, 'tmp/iut_wall/logs'); fs.mkdirSync(LOGDIR,{recursive:true});
const oleanOf = (m) => path.join(OUT, m.split('.').join('/') + '.olean');
const fileOf = (m) => path.join(ROOT, m.split('.').join('/') + '.lean');
const topo = fs.readFileSync(path.join(ROOT,'tmp/iut_wall/closure_modules.txt'),'utf8').split('\n').filter(Boolean);
const allowedPrefixes = ['Iut.Concrete.','Iut.Wall.','Iut.WallEquiv.','Iut.LogLink.','Iut.MainTheorem'];
const iutTargets = topo.filter(m => allowedPrefixes.some(p => m === p || m.startsWith(p)));
const targets = topo;
const modSet = new Set(topo);
function importsOf(m){ const f=fileOf(m); if(!fs.existsSync(f)) return []; return fs.readFileSync(f,'utf8').split('\n').filter(l=>/^import /.test(l)).map(l=>l.replace(/^import /,'').trim()); }
function ready(m){
  if(fs.existsSync(oleanOf(m))) return false; // built
  for(const im of importsOf(m)){
    if(im.startsWith('Mathlib')||im.startsWith('Lean')) continue;
    if(!fs.existsSync(oleanOf(im))) return false;
  }
  return true;
}
function compile(m){
 return new Promise(res=>{
  const f=fileOf(m), ole=oleanOf(m);
  fs.mkdirSync(path.dirname(ole),{recursive:true});
  const log=path.join(LOGDIR, m.replace(/[^A-Za-z0-9_]/g,'_')+'.log');
  const out=fs.openSync(log,'w');
  const p=spawn('lake',['env','lean','-o',ole,f],{cwd:ROOT,stdio:['ignore',out,out]});
  const t=setTimeout(()=>{ try{p.kill('SIGKILL');}catch{} }, 900000);
  p.on('close',(code)=>{ clearTimeout(t); fs.closeSync(out);
    let first=''; try{ const txt=fs.readFileSync(log,'utf8'); const line=txt.split('\n').find(l=>l.includes('error')); first=line||''; }catch{}
    res({m,code,ok:code===0 && fs.existsSync(ole),first});
  });
 });
}
let done=0, fail=0; const results=[]; let wave=0;
while(true){
  wave++;
  const readyList = targets.filter(ready);
  if(readyList.length===0) break;
  console.error('WAVE '+wave+' ready='+readyList.length);
  const batch = readyList.slice(0, 6);
  const rs = await Promise.all(batch.map(compile));
  for(const r of rs){ if(r.ok) done++; else { fail++; results.push(r); console.error('FAIL '+r.m+' exit='+r.code+' '+(r.first||'').slice(0,200)); } }
  fs.writeFileSync(path.join(ROOT,'tmp/iut_wall/progress.json'), JSON.stringify({wave,targets:targets.length,built:done,failed:fail,results},null,2));
}
const built = targets.filter(m=>fs.existsSync(oleanOf(m))).length;
const out = {targets: targets.length, built, failed: fail, results};
out.iutTargets = iutTargets.length; out.iutBuilt = iutTargets.filter(m=>fs.existsSync(oleanOf(m))).length;
fs.writeFileSync(path.join(ROOT,'tmp/iut_wall/final.json'), JSON.stringify(out,null,2));
console.log(JSON.stringify({targets:targets.length,built,failed:fail,iutTargets:iutTargets.length,iutBuilt:iutTargets.filter(m=>fs.existsSync(oleanOf(m))).length},null,2));
