import { readFileSync, writeFileSync, existsSync, statSync, mkdirSync, appendFileSync } from 'node:fs';
import { spawn, spawnSync } from 'node:child_process';
import { join, dirname } from 'node:path';
const ROOT='D:/lean'; const OUT=join(ROOT,'dag','watchdog'); mkdirSync(OUT,{recursive:true});
const MAX=Number(process.env.DAG_MAX||12); const ONCE=process.env.DAG_ONCE==='1'; const CYCLE_MS=Number(process.env.DAG_CYCLE_MS||30000);
const RESULTS=join(ROOT,'tmp','xif_guarded_results.log'); const LOG=join(OUT,'watchdog.log'); const STATE=join(OUT,'state.json');
const log=(s)=>{ const line=new Date().toISOString()+' '+s; appendFileSync(LOG,line+'\n'); console.log(line); };
const state=()=>{ try{ return JSON.parse(readFileSync(STATE,'utf8')); }catch{ return {}; } };
const saveState=(s)=>writeFileSync(STATE,JSON.stringify(s,null,2));
const regenPlan=()=>{ for(const s of ['tools/dag_plan.mjs','tools/dag_plan_deps.mjs']){ const r=spawnSync(process.execPath,[s],{cwd:ROOT,encoding:'utf8'}); if(r.status!==0){ log('PLAN FAILED '+s+' '+String(r.stderr||'').slice(0,200)); return false; } } return true; };
const oleanTarget=(p)=>{ const ported=ROOT+'/tmp/external/ported/';
  if(p.startsWith(ported)){ const rest=p.slice(ported.length); const pkg=rest.split('/')[0]; const pkgRoot=ported+pkg; const modRel=rest.split('/').slice(1).join('/').replace(/\.lean$/,''); return { root:pkgRoot, olean:join(pkgRoot,'.lake','build','lib','lean',modRel+'.olean') }; }
  const rel=p.replace(/\.lean$/,''); return { root:ROOT, olean:join(ROOT,'.lake','build','lib','lean',rel+'.olean') }; };
const perFileLog=(p)=>join(OUT,'logs',p.replace(/[\/\\:]/g,'_')+'.log');
let running=new Map(); let pending=[]; let taskState=new Map(); let plan=null;
const loadPlan=()=>{ if(!regenPlan()) return false; plan=JSON.parse(readFileSync(join(OUT,'plan.json'),'utf8')); pending=[...plan.dirty]; taskState=new Map(); for(const p of pending) taskState.set(p,'pending'); return true; };
const depsOf=(p)=> (plan.dirty_deps&&plan.dirty_deps[p])||[];
const launch=(p)=>{ const {root,olean}=oleanTarget(p); const abs=join(ROOT,p); const out=perFileLog(p); mkdirSync(dirname(olean),{recursive:true}); mkdirSync(dirname(out),{recursive:true});
  const cmd=`lake env lean -R "${root}" -o "${olean}" "${abs}" > "${out}" 2>&1`;
  const started=Date.now(); const child=spawn('cmd.exe',['/d','/s','/c',cmd],{cwd:root,stdio:'ignore',windowsHide:true});
  taskState.set(p,'running'); running.set(p,{child,started}); log('START '+p);
  child.on('close',(code)=>{ running.delete(p); const st=state(); const srcM=statSync(abs).mtimeMs;
    if(code===0){ taskState.set(p,'done'); delete st[p]; log('DONE EXIT=0 '+p+' ('+Math.round((Date.now()-started)/1000)+'s)'); }
    else { taskState.set(p,'failed'); st[p]={failed_exit:code,failed_mtime:srcM,failed_at:Date.now()}; log('FAIL EXIT='+code+' '+p); }
    saveState(st); appendFileSync(RESULTS,'EXIT='+code+' FILE='+p+'\n'); }); };
const cycle=()=>{ if(!loadPlan()) return false; log('CYCLE dirty='+pending.length+' max='+MAX);
  let guard=0;
  while(true){ guard++; if(guard>100000) break;
    let progress=false;
    for(const p of pending){ const st=taskState.get(p); if(st!=='pending') continue; const ds=depsOf(p);
      if(ds.some(d=>['failed','skipped'].includes(taskState.get(d)))){ taskState.set(p,'skipped'); log('SKIP (dep failed) '+p); progress=true; continue; }
      if(ds.every(d=>taskState.get(d)==='done')){ if(running.size<MAX){ launch(p); progress=true; } } }
    if(running.size===0 && [...taskState.values()].every(v=>v!=='pending'&&v!=='running')) break;
    if(!progress){ const t=Date.now(); while(Date.now()-t<200){} } else { const t=Date.now(); while(Date.now()-t<150){} } }
  return true; };
const heartbeat=()=>{ writeFileSync(join(OUT,'heartbeat.json'),JSON.stringify({at:new Date().toISOString(),running:running.size,pending:pending.length,statuses:[...taskState.entries()]},null,2)); };
const main=async()=>{ log('WATCHDOG START max='+MAX+' once='+ONCE);
  if(!loadPlan()){ log('initial plan failed'); if(ONCE) process.exit(2); }
  while(true){ await new Promise(r=>setTimeout(r,0)); await new Promise(async (resolve)=>{
      const ok=loadPlan(); if(!ok){ log('plan failed; sleeping'); setTimeout(resolve,CYCLE_MS); return; } log('CYCLE dirty='+pending.length+' max='+MAX); let guard=0;
      while(true){ guard++; if(guard>200000){log('guard break');break;}
        for(const p of pending){ const st=taskState.get(p); if(st!=='pending') continue; const ds=depsOf(p);
          if(ds.some(d=>['failed','skipped'].includes(taskState.get(d)))){ taskState.set(p,'skipped'); log('SKIP '+p); continue; }
          if(ds.every(d=>taskState.get(d)==='done') && running.size<MAX) launch(p); }
        heartbeat();
        if(running.size===0 && [...taskState.values()].every(v=>v!=='pending'&&v!=='running')) break;
        await new Promise(r=>setTimeout(r,300)); }
      const tally={}; for(const v of taskState.values()) tally[v]=(tally[v]||0)+1; log('BATCH DONE '+JSON.stringify(tally)); resolve(); });
    if(ONCE){ log('ONCE complete'); process.exit(0); } await new Promise(r=>setTimeout(r,CYCLE_MS)); } };
main();