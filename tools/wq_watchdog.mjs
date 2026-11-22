#!/usr/bin/env node
// Simple one-shot queue watchdog: check imports, compile, dequeue regardless.
import { readFileSync, writeFileSync, existsSync, mkdirSync, statSync } from 'node:fs';
import { spawn } from 'node:child_process';
import { join, dirname, resolve } from 'node:path';
const ROOT='D:/lean';
const OUT=ROOT+'/dag/watchdog';
const QUEUE=OUT+'/queue.txt';
const LOG=OUT+'/wq.log';
const MAX=Number(process.env.WQ_MAX||12);
const CYCLE=Number(process.env.WQ_CYCLE_MS||2000);
const norm=p=>p.trim().replaceAll('\\','/');
const readQueue=()=>{ if(!existsSync(QUEUE)) return []; return [...new Set(readFileSync(QUEUE,'utf8').split(/\r?\n/).map(norm).filter(Boolean))]; };
const writeQueue=xs=>writeFileSync(QUEUE,[...new Set(xs)].join('\n')+(xs.length?'\n':''));
const log=msg=>{ const line=new Date().toISOString()+' '+msg; try{ writeFileSync(LOG, (existsSync(LOG)?readFileSync(LOG,'utf8'):'')+line+'\n'); }catch{} console.log(line); };
const oleanForModule=m=>{
  if(m.startsWith('Mathlib.')) return join(ROOT,'.lake/packages/mathlib/.lake/build/lib/lean',m.replaceAll('.','/')+'.olean');
  return join(ROOT,'.lake/build/lib/lean',m.replaceAll('.','/')+'.olean');
};
const fileForModule=m=>{
  if(m.startsWith('Mathlib.')) return join(ROOT,'.lake/packages/mathlib',m.replaceAll('.','/')+'.lean');
  if(m.startsWith('tmp.external.ported.')){ const rest=m.slice('tmp.external.ported.'.length); return join(ROOT,'tmp/external/ported',rest.replaceAll('.','/')+'.lean'); }
  return join(ROOT,m.replaceAll('.','/')+'.lean');
};
const importsOf=(p)=>{
  const s=readFileSync(p,'utf8');
  const out=[];
  for(const line of s.split(/\r?\n/)){
    const m=line.match(/^\s*(?:public\s+)?import\s+([A-Za-z0-9_.]+)\s*$/);
    if(m) out.push(m[1]);
  }
  return out;
};
const targetRoot=(p)=>{
  if(p.startsWith('tmp/external/ported/')){ const rest=p.slice('tmp/external/ported/'.length); const pkg=rest.split('/')[0]; return join(ROOT,'tmp/external/ported',pkg); }
  return ROOT;
};
const targetOlean=(p)=>{
  const root=targetRoot(p);
  const rel=p;
  if(root===ROOT) return join(ROOT,'.lake/build/lib/lean',rel.replace(/\.lean$/,'')+'.olean');
  // ported package: path relative to package root
  const rest=rel.slice('tmp/external/ported/'.length).split('/').slice(1).join('/');
  return join(root,'.lake/build/lib/lean',rest.replace(/\.lean$/,'')+'.olean');
};
const running=new Map();
const launch=(p)=>{
  const abs=join(ROOT,p); const root=targetRoot(p); const olean=targetOlean(p);
  mkdirSync(dirname(olean),{recursive:true});
  const logPath=join(OUT,'logs',p.replace(/[\/\\:]/g,'_')+'.log');
  mkdirSync(dirname(logPath),{recursive:true});
  const started=Date.now();
  const child=spawn('lake',['env','lean','-R',root,'-o',olean,abs],{cwd:root,stdio:['ignore','pipe','pipe'],windowsHide:true});
  let out=''; child.stdout.on('data',d=>out+=d); child.stderr.on('data',d=>out+=d);
  const rec={p,child,started,out:()=>out,logPath}; running.set(p,rec);
  log('START '+p);
  child.on('close',code=>{
    try{ writeFileSync(logPath, out); }catch{}
    running.delete(p);
    if(code===0) log('DONE '+p+' ('+Math.round((Date.now()-started)/1000)+'s)');
    else log('FAIL '+p+' code='+code);
    writeQueue(readQueue().filter(x=>x!==p));
  });
};
const tick=async()=>{
  const q=readQueue();
  const blocked=[];
  const ready=[];
  for(const p of q){
    const abs=join(ROOT,p);
    if(!existsSync(abs)){ log('BLOCKED '+p+' missing source'); blocked.push(p); continue; }
    let imps=[]; try{ imps=importsOf(abs); }catch(e){ log('BLOCKED '+p+' read error'); blocked.push(p); continue; }
    const missing=imps.filter(m=>{ const o=oleanForModule(m); return !existsSync(o) && existsSync(fileForModule(m)); });
    if(missing.length){ log('BLOCKED '+p+' missing '+missing.slice(0,3).join(',')); blocked.push(p); continue; }
    ready.push(p);
  }
  if(blocked.length) writeQueue(readQueue().filter(x=>!blocked.includes(x)));
  for(const p of ready.slice(0,MAX-running.size)){
    if(!readQueue().includes(p)) continue;
    launch(p);
  }
  if(blocked.length===0 && ready.length===0 && running.size===0){ await new Promise(r=>setTimeout(r,CYCLE)); }
  else await new Promise(r=>setTimeout(r,500));
};
const main=async()=>{ mkdirSync(OUT,{recursive:true}); mkdirSync(OUT+'/logs',{recursive:true}); log('WQ WATCHDOG START max='+MAX); while(true) await tick(); };
main();
