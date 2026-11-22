#!/usr/bin/env node
// Build lana_latest Iut MainTheorem chain (Anabelian->Cor312->Implication->Tower->Tripod->MainTheorem), A873.
import fs from 'node:fs'; import path from 'node:path'; import { spawn } from 'node:child_process';
const ROOT=process.cwd();
const OUT=path.join(ROOT,'.lake/build/lib/lean');
const LOGDIR=path.join(ROOT,'tmp/iut_mt/logs'); fs.mkdirSync(LOGDIR,{recursive:true});
const oleanOf=m=>path.join(OUT,m.split('.').join('/')+'.olean');
const fileOf=m=>path.join(ROOT,m.split('.').join('/')+'.lean');
function listTree(root){ const out=[]; (function walk(d){ for(const e of fs.readdirSync(d,{withFileTypes:true})){ if(e.name==='.lake'||e.name==='.git') continue; const q=path.join(d,e.name); if(e.isDirectory()) walk(q); else if(e.name.endsWith('.lean')) out.push(q); } })(root); return out; }
const treeFiles = listTree(path.join(ROOT,'tmp/sheaf/lana_latest')).concat(listTree(path.join(ROOT,'tmp/sheaf/lana')));
const allMods = treeFiles.map(f=>f.replace(ROOT+path.sep,'').replace(/\.lean$/,'').split(path.sep).join('/').split('/').join('.'));
const modSet=new Set(allMods);
// target group modules
const groupPrefixes=['tmp.sheaf.lana_latest.Iut.Anabelian.','tmp.sheaf.lana_latest.Iut.Cor312.','tmp.sheaf.lana_latest.Iut.Implication.','tmp.sheaf.lana_latest.Iut.Tower.','tmp.sheaf.lana_latest.Iut.Tripod.'];
const targets = allMods.filter(m=>groupPrefixes.some(p=>m.startsWith(p)) || m==='tmp.sheaf.lana_latest.Iut.MainTheorem');
// dependency closure of targets (all trees), excluding shehdd-owned paths
const shehddOwned = (m)=> m.includes('.Iut.Wall.')||m.includes('.Iut.WallEquiv.')||m.includes('padic_log_volume');
const closure=new Set(); const stack=[...targets];
while(stack.length){ const m=stack.pop(); if(closure.has(m)) continue; closure.add(m);
  const f=fileOf(m); if(!fs.existsSync(f)) continue;
  for(const line of fs.readFileSync(f,'utf8').split('\n')){
    const mm=line.match(/^import\s+([A-Za-z0-9_.]+)/); if(!mm) continue;
    const im=mm[1];
    if(im.startsWith('Mathlib')||im.startsWith('Lean')||im==='Mathlib') continue;
    if(im.startsWith('tmp.sheaf.lana')){ if(!closure.has(im)) stack.push(im); }
  }
}
const buildable=[...closure].filter(m=>!shehddOwned(m));
const priority=(m)=> m.includes('.Iut.Anabelian.')?0 : m.includes('.Iut.Cor312.')?1 : m.includes('.Iut.Concrete.')?2 : m.includes('.Iut.Implication.')?3 : m.includes('.Iut.Tower.')?4 : m.includes('.Iut.Tripod.')?5 : m==='tmp.sheaf.lana_latest.Iut.MainTheorem'?6 : 7;
function importsOf(m){ const f=fileOf(m); if(!fs.existsSync(f)) return []; return fs.readFileSync(f,'utf8').split('\n').filter(l=>/^import /.test(l)).map(l=>l.replace(/^import /,'').trim()); }
function ready(m){ if(fs.existsSync(oleanOf(m))) return false; for(const im of importsOf(m)){ if(im.startsWith('Mathlib')||im.startsWith('Lean')) continue; if(!fs.existsSync(oleanOf(im))) return false; } return true; }
function compile(m){ return new Promise(res=>{ const f=fileOf(m), ole=oleanOf(m); fs.mkdirSync(path.dirname(ole),{recursive:true});
  const log=path.join(LOGDIR,m.replace(/[^A-Za-z0-9_]/g,'_')+'.log'); const out=fs.openSync(log,'w');
  const p=spawn('lake',['env','lean','-o',ole,f],{cwd:ROOT,stdio:['ignore',out,out]}); const t=setTimeout(()=>{try{p.kill('SIGKILL')}catch{}},1200000);
  p.on('close',code=>{clearTimeout(t); try{fs.closeSync(out)}catch{}; let first=''; try{const txt=fs.readFileSync(log,'utf8'); first=(txt.split('\n').find(l=>l.includes('error'))||'')}catch{}; res({m,code,ok:code===0&&fs.existsSync(ole),first});}); }); }
let fail=0; const results=[]; const start=Date.now(); let report=0;
while(true){
  const unbuilt=buildable.filter(m=>!fs.existsSync(oleanOf(m)));
  if(unbuilt.length===0) break;
  const readyList=unbuilt.filter(ready).sort((a,b)=>priority(a)-priority(b));
  if(readyList.length===0){ if(Date.now()-start>45*60*1000){ console.error('STOP waiting deps'); break; } console.error('WAIT deps unbuilt='+unbuilt.length); await new Promise(r=>setTimeout(r,60000)); continue; }
  const batch=readyList.slice(0,5);
  console.error('BATCH ready='+readyList.length+' '+batch.map(m=>m.split('.').slice(-1)[0]).join(','));
  const rs=await Promise.all(batch.map(compile));
  for(const r of rs){ if(!r.ok){ fail++; results.push(r); console.error('FAIL '+r.m+' exit='+r.code+' '+(r.first||'').slice(0,160)); } }
  const built=buildable.filter(m=>fs.existsSync(oleanOf(m))).length;
  report++;
  fs.writeFileSync(path.join(ROOT,'tmp/iut_mt/progress.json'), JSON.stringify({total:buildable.length,built,failed:fail,results},null,2));
  if(report%4===0) console.error('PROGRESS '+built+'/'+buildable.length);
}
const summary={total:buildable.length,built:buildable.filter(m=>fs.existsSync(oleanOf(m))).length,failed:fail};
fs.writeFileSync(path.join(ROOT,'tmp/iut_mt/final.json'),JSON.stringify(summary,null,2));
console.log(JSON.stringify(summary,null,2));
