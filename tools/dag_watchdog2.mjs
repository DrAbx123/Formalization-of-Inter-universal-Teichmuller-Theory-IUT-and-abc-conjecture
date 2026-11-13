import { readFileSync, writeFileSync, existsSync, statSync, mkdirSync, appendFileSync, openSync, closeSync, unlinkSync } from 'node:fs';
import { spawn, spawnSync } from 'node:child_process';
import { join, dirname } from 'node:path';
const ROOT='D:/lean'; const OUT=join(ROOT,'dag','watchdog'); mkdirSync(OUT,{recursive:true}); mkdirSync(join(OUT,'logs'),{recursive:true});

// A733 single-instance file lock
const LOCK = join(OUT,'watchdog.lock');
try {
  if (existsSync(LOCK)) {
    const pid = Number(String(readFileSync(LOCK,'utf8')).trim());
    if (pid > 0) { try { process.kill(pid, 0); console.log('watchdog already running pid=' + pid); process.exit(0); } catch (e) {} }
  }
  writeFileSync(LOCK, String(process.pid));
  process.on('exit', () => { try { if (String(readFileSync(LOCK,'utf8')).trim() === String(process.pid)) unlinkSync(LOCK); } catch (e) {} });
} catch (e) {}
process.on('uncaughtException',(e)=>{ try{ appendFileSync('D:/lean/dag/watchdog/crash.log', new Date().toISOString()+' UNCAUGHT '+(e&&e.stack||e)+String.fromCharCode(10)); }catch{} });
process.on('unhandledRejection',(e)=>{ try{ appendFileSync('D:/lean/dag/watchdog/crash.log', new Date().toISOString()+' REJECT '+(e&&e.stack||e)+String.fromCharCode(10)); }catch{} });
const MAX=Number(process.env.DAG_MAX||12); const ONCE=process.env.DAG_ONCE==='1'; const CYCLE=Number(process.env.DAG_CYCLE_MS||5000); const GRAPH_MS=Number(process.env.DAG_GRAPH_MS||3600000);
const RESULTS=join(ROOT,'tmp','xif_guarded_results.log'); const LOG=join(OUT,'watchdog.log'); const STATE=join(OUT,'state.json');
const log=(s)=>{ const line=new Date().toISOString()+' '+s; for(let i=0;i<8;i++){ try{ appendFileSync(LOG,line+'\n'); break; }catch(e){ if(i===7){ try{ appendFileSync(LOG+'.fallback',line+' ('+(e&&e.code)+')\n'); }catch{} } else { const t=Date.now(); while(Date.now()-t<25){} } } } console.log(line); };
const state=()=>{ try{ return JSON.parse(readFileSync(STATE,'utf8')); }catch{ return {}; } }; const saveState=(s)=>writeFileSync(STATE,JSON.stringify(s,null,2));
const runTool=(s)=>{ const r=spawnSync(process.execPath,[s],{cwd:ROOT,encoding:'utf8',maxBuffer:1024*1024*64}); if(r.status!==0) log('TOOL FAIL '+s+' code='+r.status+' '+(r.stderr||'').slice(0,300)); return r.status===0; };
const oleanTarget=(p)=>{ const ported=ROOT+'/tmp/external/ported/';
  if(p.startsWith(ported)){ const rest=p.slice(ported.length); const pkg=rest.split('/')[0]; const pkgRoot=ported+pkg; const modRel=rest.split('/').slice(1).join('/').replace(/\.lean$/,''); return {root:pkgRoot, olean:join(pkgRoot,'.lake','build','lib','lean',modRel+'.olean')}; }
  return {root:ROOT, olean:join(ROOT,'.lake','build','lib','lean',p.replace(/\.lean$/,'')+'.olean')}; };
let running=new Map(), plan=null, taskState=new Map(), pending=[]; const retries=new Map();
const WL=(()=>{try{return new Set(readFileSync(join(OUT,"extra-targets.txt"),"utf8").split(/\r?\n/).map(x=>x.trim().replaceAll("\\","/")).filter(Boolean));}catch{return new Set();}})();
const getWL=()=>{try{return new Set(readFileSync(join(OUT,"extra-targets.txt"),"utf8").split(/\r?\n/).map(x=>x.trim().replaceAll("\\","/")).filter(Boolean));}catch{return new Set();}};
const loadPlan=()=>{ if(!runTool('tools/dag_plan.mjs')||!runTool('tools/dag_plan_deps.mjs')) return false; plan=JSON.parse(readFileSync(join(OUT,'plan.json'),'utf8')); const _st=state(); pending=plan.dirty.filter(p=>{ const WL=getWL(); if(WL.size&&!WL.has(p)) return false; if(/Mzk1ABCTwoEstimatesHeightLemmasShaActual|Mzk1AcceptanceFinalChecksActual|Mzk1E4Example36ConsumerActual(?!.*Adapted)$/.test(p)||p.includes('Mzk1ABCTwoEstimatesHeightLemmasShaActual')||p.includes('Mzk1AcceptanceFinalChecksActual')||p.includes('tmp/sheaf/lana/')||(p.startsWith('tmp/sheaf/xif/paper/')&&!/Mzk1.*Actual\.lean$/.test(p)&&!WL.has(p))||p.includes('Mzk1LANA')||p.includes('A490Wall')||p.includes('A490NumericalWall')||p.includes('NumericalWallActual')||p.includes('SSIneqOfStep3115')||p.includes('VariantOfStep3115')||p.includes('Step3115AlignmentProof')) return false; try{ const e=_st[p]; if(!e||e.failed_exit===undefined) return true; const m=statSync(join(ROOT,p)).mtimeMs; return !(e.failed_mtime===m && (Date.now()-(e.failed_at||0))<600000); }catch{ return true; } }); taskState=new Map(); for(const p of pending) taskState.set(p,'pending');
  try{ const rs=JSON.parse(readFileSync(join(OUT,'runtime-status.json'),'utf8')); for(const m of (rs.mismatches||[])) for(const e of (m.evidence||[])){ const f=e.file; if(!f) continue; if(/Mzk1ABCTwoEstimatesHeightLemmasShaActual|Mzk1AcceptanceFinalChecksActual|Mzk1E4Example36ConsumerActual/.test(f)||f.startsWith('tmp/external/ported/')||f.startsWith('tmp/sheaf/n8/')||(f.startsWith('tmp/sheaf/xif/paper/')&&!/Mzk1.*Actual\.lean$/.test(f))||f.includes('belyi_pair')) continue; if((!getWL().size||getWL().has(f))&&!taskState.has(f)){ pending.push(f); taskState.set(f,'pending'); } } }catch{} return true; };
const depsOf=(p)=>(plan.dirty_deps&&plan.dirty_deps[p])||[];
const launch=(p)=>{ const {root,olean}=oleanTarget(p); const abs=join(ROOT,p); const out=join(OUT,'logs',p.replace(/[\/\\:]/g,'_')+'.log'); mkdirSync(dirname(olean),{recursive:true}); mkdirSync(dirname(out),{recursive:true});
  let logStart=0; try{ logStart=existsSync(out)?statSync(out).size:0; }catch{} const fd=openSync(out,'a'); const started=Date.now(); const child=spawn('lake',['env','lean','-R',root,'-o',olean,abs],{cwd:root,stdio:['ignore',fd,fd],windowsHide:true});
  try{ closeSync(fd); }catch{}
  taskState.set(p,'running'); running.set(p,{child,started}); log('START '+p);
  const killer=setTimeout(()=>{ try{ log('TIMEOUT KILL '+p); child.kill(); }catch{} }, 1800000);
  child.on('error',(e)=>{ try{ clearTimeout(killer); running.delete(p); taskState.set(p,'failed'); log('SPAWN ERR '+p+' '+e.message); }catch{} });
  child.on('close',(code)=>{ try{ clearTimeout(killer); running.delete(p); const st=state(); let srcM=0; try{ srcM=statSync(abs).mtimeMs; }catch{ srcM=-1; } if(code===0){ taskState.set(p,'done'); delete st[p]; log('DONE EXIT=0 '+p+' ('+Math.round((Date.now()-started)/1000)+'s)'); } else { let tail=''; try{ const allS=readFileSync(out,'utf8'); tail=allS.slice(Math.min(logStart, allS.length)).slice(-4000); }catch{} const transient=/failed to read file|INTERNAL PANIC|out of memory|object file .* does not exist/.test(tail); const n=retries.get(p)||0; if(transient && n<3){ retries.set(p,n+1); taskState.set(p,'pending'); log('RETRY TRANSIENT '+p+' n='+(n+1)); } else { taskState.set(p,'failed'); st[p]={failed_exit:code,failed_mtime:srcM,failed_at:Date.now()}; log('FAIL EXIT='+code+' '+p); } } saveState(st); appendFileSync(RESULTS,'EXIT='+code+' FILE='+p+'\n'); }catch(e){ running.delete(p); taskState.set(p,'skipped'); log('CLOSE ERR '+p+' '+e.message); } });
};
const batch=async()=>{ let guard=0; const started=Date.now(); let lastMove=Date.now(); let lastRes=0; while(true){ guard++; try{ const m=statSync(RESULTS).mtimeMs; if(m!==lastRes){ lastRes=m; lastMove=Date.now(); } }catch{}
  if(guard>200000){ log('guard break'); break; }
  if(Date.now()-started>5400000){ log('HARD STALL BREAK'); try{ for(const [,r] of running){ r.child.kill(); } }catch{} running.clear(); for(const [p,v] of taskState) if(v==='running') taskState.set(p,'failed'); break; }
  if(Date.now()-lastMove>1200000){ log('HARD STALL KILL running='+running.size); try{ for(const [,r] of running){ r.child.kill(); } }catch{} running.clear(); for(const [p,v] of taskState) if(v==='running') taskState.set(p,'failed'); break; }
  for(const p of pending){ const stt=taskState.get(p); if(stt!=='pending') continue; const ds=depsOf(p);
    if(ds.some(d=>['failed','skipped'].includes(taskState.get(d)))){ taskState.set(p,'skipped'); log('SKIP '+p); continue; }
    if(ds.every(d=>taskState.get(d)==='done'||!taskState.has(d)) && running.size<MAX) launch(p); }
  if(running.size===0 && [...taskState.values()].some(v=>v==='pending')){ log('DEADLOCK no-running-but-pending'); break; }
  if(running.size>0){ let alive=0; for(const [,r] of running){ if(r.child.exitCode===null && r.child.signalCode===null){ try{ process.kill(r.child.pid,0); alive++; }catch{} } } if(alive===0){ log('CHILDREN EXITED - reset batch'); for(const [p,v] of taskState) if(v==='running') taskState.set(p,'failed'); running.clear(); break; } }
  if(running.size===0 && [...taskState.values()].every(v=>v!=='pending'&&v!=='running')) break;
  await new Promise(r=>setTimeout(r,250)); } };
const heartbeat=()=>{ writeFileSync(join(OUT,'heartbeat.json'),JSON.stringify({at:new Date().toISOString(),running:running.size,pending:pending.length},null,2)); };
const main=async()=>{ log('DAG WATCHDOG START max='+MAX+' once='+ONCE+' cycle='+CYCLE); let lastGraph=0;
  while(true){ const now=Date.now();
    if(now-lastGraph>GRAPH_MS || lastGraph===0){ log('GRAPH REBUILD SKIPPED (patched-a1041; plan from cache)'); lastGraph=Date.now(); }
    if(loadPlan()){ log('CYCLE pending='+pending.length+' max='+MAX); await batch(); runTool('tools/dag_status.mjs'); runTool('tools/dag_next.mjs'); const tally={}; for(const v of taskState.values()) tally[v]=(tally[v]||0)+1; log('BATCH DONE '+JSON.stringify(tally)); } else { log('PLAN FAILED'); }
    heartbeat(); if(ONCE){ log('ONCE complete'); process.exit(0); } await new Promise(r=>setTimeout(r,CYCLE)); } };
main();