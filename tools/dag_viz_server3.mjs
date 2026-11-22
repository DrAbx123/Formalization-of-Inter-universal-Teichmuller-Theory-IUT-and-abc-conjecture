import http from 'node:http';
import { readFileSync } from 'node:fs';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';
const ROOT='D:/lean'; const PORT=18765;
const readJson=(p,f)=>{ try{ return JSON.parse(readFileSync(p,'utf8')); }catch{ return f; } };
const readTail=(p,n)=>{ try{ return readFileSync(p,'utf8').split(/\r?\n/).slice(-n); }catch{ return []; } };
let leanCache={t:0,n:0};
const leanCount=()=>{ const now=Date.now(); if(now-leanCache.t<8000) return leanCache.n; try{ const r=spawnSync('tasklist',['/FI','IMAGENAME eq lean.exe','/FO','CSV','/NH'],{encoding:'utf8',windowsHide:true}); leanCache={t:now,n:(r.stdout||'').split(/\r?\n/).filter(l=>/lean\.exe/i.test(l)).length}; }catch{} return leanCache.n; };
let cache={t:0,data:null};
const build=()=>{
  const dag=readJson(join(ROOT,'dag','declaration-dag.json'),{nodes:[],edges:[]});
  const rt=readJson(join(ROOT,'dag','watchdog','runtime-status.json'),{nodes:[]});
  const blockers=readJson(join(ROOT,'coord','DAG-BLOCKED.json'),{blocked:[]}).blocked||[];
  const plan=readJson(join(ROOT,'dag','watchdog','plan.json'),{dirty:[]});
  const rtMap=new Map(); for(const n of (rt.nodes||[])) rtMap.set(n.id,n);
  const blocked=new Set(blockers.map(b=>b.id));
  const baseNodes=(dag.nodes||[]).map(n=>{ const r=rtMap.get(n.id); return {id:n.id,kind:n.kind,title:n.title||'',status:n.status,files:(n.files||[]).slice(0,4),note:(n.note||'').slice(0,160),blocked:blocked.has(n.id),mismatch:r?!!r.mismatch:false,fresh:r?!!r.all_fresh:null,exits_ok:r?!!r.exits_ok:null}; });
  const nodes=baseNodes; const edgeList=(dag.edges||[]).map(e=>({from:e.from,to:e.to,kind:e.kind||'dep'}));
  const findParent=(id)=>{ let best=null; for(let i=id.length-1;i>0;i--){ const c=id[i]; if(c===':'||c==='.'){ const p=id.slice(0,i); if(realIds.has(p)&&p!==id){ if(!best||p.length>best.length) best=p; } } } return best; };
  const regionOf=(id)=>{ const i=id.indexOf(':'); return i>0?id.slice(0,i):'root'; };
  const hubIds=new Set(); const hubOf=(region)=>{ const id='HUB:'+region; if(!hubIds.has(id)){ hubIds.add(id); nodes.push({id,kind:'hub',title:'region hub ('+region+') visual only',status:'HUB',files:[],note:'visual grouping only',blocked:false,mismatch:false,fresh:null,exits_ok:null,derived:true}); } return id; };
  // NO grouping/hubs: only real DAG edges
  const byStatus={}, byKind={}; for(const n of (dag.nodes||[])){ byStatus[n.status]=(byStatus[n.status]||0)+1; byKind[n.kind]=(byKind[n.kind]||0)+1; }
  const results=readTail(join(ROOT,'tmp','xif_guarded_results.log'),30).filter(Boolean);
  const watchdogLog=readTail(join(ROOT,'dag','watchdog','watchdog.log'),16).filter(Boolean);
  return {generated_at:new Date().toISOString(),stats:{nodes:(dag.nodes||[]).length,edges:(dag.edges||[]).length,byStatus,byKind,blocked:blockers.length,dirty:(plan.dirty||[]).length,lean:leanCount()},nodes,edges:edgeList,recent_results:results,watchdog_log:watchdogLog};
};
const html=String.raw`<!doctype html><html><head><meta charset='utf-8'><title>DAG Live</title><style>
*{box-sizing:border-box}html,body{margin:0;height:100%;background:#0b0f14;color:#dfe7ef;font:13px/1.45 Consolas,monospace}
#cards-view{height:100%;display:flex;flex-direction:column}
header{background:#111820;padding:10px 16px;border-bottom:1px solid #263242;display:flex;gap:16px;align-items:center;flex-wrap:wrap}
h1{font-size:15px;margin:0;color:#7fd1ff}.stat b{color:#8ef0a8}.muted{color:#7d8ea3}
#filters{margin:8px 16px;display:flex;gap:8px;flex-wrap:wrap;align-items:center}
input{background:#101820;border:1px solid #2b3a4d;color:#dfe7ef;padding:5px 8px;border-radius:4px;width:240px}
.chip{cursor:pointer;border:1px solid #2b3a4d;border-radius:10px;padding:2px 10px;background:#101820;user-select:none}.chip.on{background:#1d3b55;border-color:#4ea4dc}
#grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(360px,1fr));gap:8px;padding:8px 16px 40px;overflow:auto;flex:1}
.node{background:#0f1620;border:1px solid #223041;border-left:4px solid #555;border-radius:5px;padding:7px 9px;cursor:pointer;overflow:hidden}
.node:hover{background:#14202c}.node .id{color:#9fd8ff;font-weight:bold;word-break:break-all}
.node .t{color:#8fa3b8;margin:2px 0;max-height:34px;overflow:hidden}.node .f{color:#6d8298;font-size:11px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.bad{color:#ff9b9b}.good{color:#8ef0a8}.warn{color:#ffd479}
#ticker{padding:0 16px 10px;color:#9fb3c8;font-size:12px;max-height:90px;overflow:auto;border-top:1px solid #1d2937}
#detail{position:fixed;right:0;top:0;bottom:0;width:430px;background:#101a24;border-left:1px solid #2b3a4d;padding:12px;overflow:auto;display:none;z-index:30}
#detail pre{white-space:pre-wrap;color:#a9c3d8}
#graph-view{display:none;position:fixed;inset:0;z-index:10;background:#0b0f14}
#gcanvas{position:absolute;inset:0;width:100%;height:100%;display:block;cursor:grab}
#gbar{position:absolute;top:10px;left:10px;right:10px;display:flex;gap:10px;align-items:center;flex-wrap:wrap;background:rgba(13,20,28,.86);border:1px solid #263242;border-radius:8px;padding:8px 12px;z-index:12}
#gbar .chip{background:#152538}#gnote{position:absolute;bottom:10px;left:12px;color:#7d8ea3;font-size:12px;z-index:12}
</style></head><body>
<div id='cards-view'>
<header><h1>IUT DAG LIVE</h1>
<span class='stat'>nodes <b id='sn'>-</b></span><span class='stat'>edges <b id='se'>-</b></span><span class='stat'>blocked <b id='sb'>-</b></span><span class='stat'>dirty <b id='sd'>-</b></span><span class='stat'>lean <b id='sl'>-</b></span><span class='muted' id='st'></span>
<span class='chip' id='modeBtn'>DEP GRAPH</span></header>
<div id='filters'><input id='q' placeholder='search id/title/file'> <span id='chips'></span></div>
<div id='grid'></div><div id='ticker'></div></div>
<div id='graph-view'><canvas id='gcanvas'></canvas>
<div id='gbar'><span class='chip' id='backBtn'>BACK TO CARDS</span><span class='chip' id='fitBtn'>FIT</span><input id='q2' placeholder='search (graph)'><span class='muted' id='gstats'></span></div>
<div id='gnote'>damped edge springs + damped up/down arrow force (E-field) · inelastic node collisions · no gravity · no other forces · wheel zoom · drag pan/node · click details · ESC cards</div></div>
<div id='detail'></div>
<script>
let DATA=null,FILT=new Set(),Q='',MODE='cards',HOVER=null,SEL=null,DRAG=null,DRAGPAN=null,PAN={s:1,ox:0,oy:0},FITTED=0;
const POS=new Map();
const col={PROVED:'#2ecc71',BOTTOM:'#1abc9c',CONDITIONAL:'#f1c40f',NAMED:'#e67e22',GAP:'#e74c3c',TREE_ASSET:'#3498db',DEF:'#95a5a6',EXTERNAL:'#9b59b6'};
function esc(s){return (s||'').replace(/[&<>]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;'}[c]))}
function statsInit(){ if(!DATA) return; const d=DATA; document.getElementById('sn').textContent=d.stats.nodes; document.getElementById('se').textContent=d.stats.edges; document.getElementById('sb').textContent=d.stats.blocked; document.getElementById('sd').textContent=d.stats.dirty; const l=document.getElementById('sl'); if(l) l.textContent=d.stats.lean;
 const st=Object.entries(d.stats.byStatus).map(([k,v])=>k+':'+v).join('  '); document.getElementById('st').textContent=st;
 const gs=document.getElementById('gstats'); if(gs) gs.textContent='nodes '+d.stats.nodes+'  edges '+d.stats.edges+'  blocked '+d.stats.blocked;
 const statuses=Object.keys(d.stats.byStatus).sort(); const chips=document.getElementById('chips'); chips.innerHTML='';
 const all=document.createElement('span'); all.className='chip'+(FILT.size?'':' on'); all.textContent='ALL'; all.onclick=()=>{FILT.clear();render()}; chips.appendChild(all);
 for(const s of statuses){ const c=document.createElement('span'); c.className='chip'+(FILT.has(s)?' on':''); c.textContent=s; c.onclick=()=>{FILT.has(s)?FILT.delete(s):FILT.add(s);render()}; chips.appendChild(c); } }
function render(){ if(!DATA) return; statsInit(); const q=(Q||'').toLowerCase(); const list=DATA.nodes.filter(n=>{ if(n.kind==='hub') return false; if(FILT.size&&!FILT.has(n.status)) return false; if(!q) return true; return (n.id+' '+n.title+' '+(n.files||[]).join(' ')).toLowerCase().includes(q); });
 const g=document.getElementById('grid'); g.innerHTML='';
 for(const n of list){ const el=document.createElement('div'); el.className='node'; el.style.borderLeftColor=n.blocked?'#e74c3c':(col[n.status]||'#555'); const b=[]; if(n.blocked) b.push('<span class=bad>BLOCKED</span>'); if(n.mismatch) b.push('<span class=warn>MISMATCH</span>'); if(n.fresh===true) b.push('<span class=good>fresh</span>'); if(n.exits_ok===false) b.push('<span class=bad>exit!=0</span>');
  el.innerHTML='<div class=id>'+esc(n.id)+'</div><div class=t><span class=chip>'+esc(n.status)+'</span> <span class=muted>'+esc(n.kind)+'</span> '+b.join(' ')+'</div><div class=t>'+esc(n.title)+'</div><div class=f>'+esc((n.files||[])[0]||'')+'</div>'; el.onclick=()=>showDetail(n); g.appendChild(el); }
 const tk=document.getElementById('ticker'); tk.innerHTML='<b>recent watchdog</b><br>'+DATA.watchdog_log.filter(l=>/START|DONE|FAIL|CYCLE|BATCH/.test(l)).slice(-8).map(l=>'<div>'+esc(l)+'</div>').join(''); }
function showDetail(n){ const el=document.getElementById('detail'); el.style.display='block'; el.innerHTML='<h3 style="color:#7fd1ff;margin:0 0 8px">'+esc(n.id)+'</h3><pre>'+esc(JSON.stringify(n,null,2))+'</pre><button class="chip" onclick="this.parentElement.style.display=\'none\'">close</button>'; }
function filtered(){ const q=(Q||'').toLowerCase(); return DATA.nodes.filter(n=>{ if(n.kind==='hub') return true; if(FILT.size&&!FILT.has(n.status)) return false; if(!q) return true; return (n.id+' '+n.title+' '+(n.files||[]).join(' ')).toLowerCase().includes(q); }); }
function resize(){ const c=document.getElementById('gcanvas'); const dpr=devicePixelRatio||1; c.width=Math.floor(innerWidth*dpr); c.height=Math.floor(innerHeight*dpr); c.getContext('2d').setTransform(dpr,0,0,dpr,0,0); }
function ensurePos(ns){ const W=innerWidth,H=innerHeight; const cols=Math.max(1,Math.ceil(Math.sqrt(ns.length))); const sp=Math.max(18,Math.min(46,Math.sqrt((W*H)/Math.max(1,ns.length))*0.42)); let i=0; for(const n of ns){ if(!POS.has(n.id)){ const cx=(i%cols)-(cols-1)/2; const cy=Math.floor(i/cols)-(Math.ceil(ns.length/cols)-1)/2; POS.set(n.id,{x:W/2+cx*sp,y:H/2+cy*sp,vx:0,vy:0}); } i++; } }
function setMode(m){ MODE=m; document.getElementById('cards-view').style.display=m==='graph'?'none':'flex'; document.getElementById('graph-view').style.display=m==='graph'?'block':'none'; if(m==='graph'){ resize(); FITTED=0; } }
function simStep(){ if(!DATA) return; const ns=filtered(); const W=innerWidth,H=innerHeight; ensurePos(ns); const set=new Set(ns.map(n=>n.id)); const es=(DATA.edges||[]).filter(e=>set.has(e.from)&&set.has(e.to)); const MINSEP=12;
  for(const e of es){ const a=POS.get(e.from),b=POS.get(e.to); if(!a||!b) continue; const dx=b.x-a.x,dy=b.y-a.y; let d=Math.hypot(dx,dy); if(d<0.001) d=0.001; const ux=dx/d,uy=dy/d; const rest=200; const corr=Math.max(-6,Math.min(6,d-rest))*0.5; if(!(DRAG&&DRAG.id===e.from)){ a.x+=ux*corr; a.y+=uy*corr; } if(!(DRAG&&DRAG.id===e.to)){ b.x-=ux*corr; b.y-=uy*corr; } }
  for(const e of es){ const a=POS.get(e.from),b=POS.get(e.to); if(!a||!b) continue; const F=0.6; if(!(DRAG&&DRAG.id===e.to)){ b.y-=F; } if(!(DRAG&&DRAG.id===e.from)){ a.y+=F; } }
  for(let pass=0;pass<4;pass++){ for(let i=0;i<ns.length;i++){ const a=POS.get(ns[i].id); for(let j=i+1;j<ns.length;j++){ const b=POS.get(ns[j].id); let dx=b.x-a.x,dy=b.y-a.y; let d2=dx*dx+dy*dy; if(d2>=MINSEP*MINSEP) continue; let d=Math.sqrt(d2); let ux,uy; if(d<0.001){ ux=Math.random()-0.5; uy=Math.random()-0.5; const nn=Math.hypot(ux,uy)||1; ux/=nn; uy/=nn; d=0.001; } else { ux=dx/d; uy=dy/d; } const push=(MINSEP-d)*0.5; if(!(DRAG&&DRAG.id===ns[i].id)){ a.x-=ux*push; a.y-=uy*push; } if(!(DRAG&&DRAG.id===ns[j].id)){ b.x+=ux*push; b.y+=uy*push; } } } }
  for(const n of ns){ const p=POS.get(n.id); if(!p||(DRAG&&DRAG.id===n.id)) continue; p.vx*=0.5; p.vy*=0.5; if(p.x<30)p.x=30; if(p.x>W-30)p.x=W-30; if(p.y<30)p.y=30; if(p.y>H-30)p.y=H-30; } }
function fit(){ const ns=filtered(); if(!ns.length) return; let x0=1e9,y0=1e9,x1=-1e9,y1=-1e9; for(const n of ns){ const p=POS.get(n.id); if(!p) continue; x0=Math.min(x0,p.x);y0=Math.min(y0,p.y);x1=Math.max(x1,p.x);y1=Math.max(y1,p.y); } const W=innerWidth,H=innerHeight; const s=Math.min(W/(x1-x0+36),H/(y1-y0+36)); PAN.s=Math.max(0.15,Math.min(6,s)); PAN.ox=W/2-((x0+x1)/2)*PAN.s; PAN.oy=H/2-((y0+y1)/2)*PAN.s; }
function world(mx,my){ return {x:(mx-PAN.ox)/PAN.s,y:(my-PAN.oy)/PAN.s}; }
function nearest(mx,my){ const w=world(mx,my); let best=null,bd=Math.pow(16/PAN.s,2); for(const n of filtered()){ const p=POS.get(n.id); if(!p) continue; const dx=p.x-w.x,dy=p.y-w.y,d=dx*dx+dy*dy; if(d<bd){bd=d;best=n;} } return best; }
function draw(){ if(MODE!=='graph'||!DATA) return; simStep(); const c=document.getElementById('gcanvas'); const ctx=c.getContext('2d'); const W=innerWidth,H=innerHeight; ctx.clearRect(0,0,W,H); ctx.save(); ctx.translate(PAN.ox,PAN.oy); ctx.scale(PAN.s,PAN.s);
 const ns=filtered(); const set=new Set(ns.map(n=>n.id)); const nm=new Map(ns.map(n=>[n.id,n])); const ecol={statement:'#3f6fa8',proof:'#4f9a4f',interface:'#8f6fb8',gap:'#b05f5f',dep:'#3d5266'};
 for(const e of (DATA.edges||[])){ if(!set.has(e.from)||!set.has(e.to)) continue; const a=POS.get(e.from),b=POS.get(e.to); if(!a||!b) continue; if(e.kind==='hub'){ ctx.setLineDash([3/PAN.s,6/PAN.s]); ctx.strokeStyle='#2e4258'; } else { ctx.setLineDash([]); ctx.strokeStyle=ecol[e.kind]||'#3d5266'; } ctx.lineWidth=(e.kind==='hub'?0.8:1.1)/PAN.s; ctx.beginPath();ctx.moveTo(a.x,a.y);ctx.lineTo(b.x,b.y);ctx.stroke();
  if(e.kind!=='hub'){ const dx=b.x-a.x,dy=b.y-a.y,d=Math.hypot(dx,dy)||1; const ux=dx/d,uy=dy/d; const tn=nm.get(e.to); const tr=tn&&tn.blocked?9:6; const tipX=b.x-ux*(tr+2),tipY=b.y-uy*(tr+2); const sz=8/PAN.s; ctx.fillStyle=ctx.strokeStyle; ctx.beginPath();ctx.moveTo(tipX,tipY);ctx.lineTo(tipX-ux*sz+uy*sz*0.55,tipY-uy*sz-ux*sz*0.55);ctx.lineTo(tipX-ux*sz-uy*sz*0.55,tipY-uy*sz+ux*sz*0.55);ctx.closePath();ctx.fill(); } }
 ctx.setLineDash([]);
 for(const n of ns){ const p=POS.get(n.id); if(!p) continue; const r=(n.kind==='hub'?10:(n.blocked?9:6)); ctx.beginPath();ctx.arc(p.x,p.y,r,0,6.2832); ctx.fillStyle=n.kind==='hub'?'#33465c':(n.blocked?'#e74c3c':(col[n.status]||'#888')); ctx.fill(); if(n.id===SEL||(HOVER&&n.id===HOVER.id)){ ctx.strokeStyle='#fff';ctx.lineWidth=2.5/PAN.s;ctx.stroke(); } }
 ctx.restore(); if(HOVER){ const p=POS.get(HOVER.id); if(p){ const sx=p.x*PAN.s+PAN.ox,sy=p.y*PAN.s+PAN.oy; ctx.fillStyle='#dfe7ef';ctx.font='13px Consolas';ctx.fillText(HOVER.id,sx+12,sy-10); } }
 if(FITTED<2){ FITTED++; fit(); } }
function loop(){ draw(); requestAnimationFrame(loop); }
function bindSeq(){ const c=document.getElementById('gcanvas');
 c.addEventListener('mousemove',e=>{ if(DRAG){ const w=world(e.offsetX,e.offsetY); DRAG.x=w.x;DRAG.y=w.y; } else { HOVER=nearest(e.offsetX,e.offsetY); c.style.cursor=HOVER?'pointer':'grab'; } });
 c.addEventListener('mousedown',e=>{ const n=nearest(e.offsetX,e.offsetY); if(n){ const p=POS.get(n.id); DRAG={id:n.id,x:p.x,y:p.y}; SEL=n.id; } else { DRAGPAN={sx:e.offsetX,sy:e.offsetY,ox:PAN.ox,oy:PAN.oy}; } });
 c.addEventListener('wheel',e=>{ e.preventDefault(); const w=world(e.offsetX,e.offsetY); const f=Math.exp(-e.deltaY*0.0012); PAN.s=Math.max(0.1,Math.min(6,PAN.s*f)); PAN.ox=e.offsetX-w.x*PAN.s; PAN.oy=e.offsetY-w.y*PAN.s; },{passive:false}); }
window.addEventListener('mousemove',e=>{ if(DRAG){ const p=POS.get(DRAG.id); if(p){ p.x=DRAG.x;p.y=DRAG.y;p.vx=0;p.vy=0; } } else if(DRAGPAN){ PAN.ox=DRAGPAN.ox+(e.clientX-DRAGPAN.sx); PAN.oy=DRAGPAN.oy+(e.clientY-DRAGPAN.sy); } });
window.addEventListener('mouseup',()=>{ if(DRAG){ const n=DATA.nodes.find(x=>x.id===DRAG.id); if(n) showDetail(n); DRAG=null; } DRAGPAN=null; });
document.getElementById('modeBtn').onclick=()=>setMode('graph'); document.getElementById('backBtn').onclick=()=>setMode('cards');
document.getElementById('fitBtn').onclick=()=>{ FITTED=0; fit(); };
document.getElementById('q').oninput=e=>{Q=e.target.value; render();}; document.getElementById('q2').oninput=e=>{Q=e.target.value; FITTED=0;};
window.addEventListener('keydown',e=>{ if(e.key==='Escape') setMode('cards'); }); window.addEventListener('resize',()=>{ if(MODE==='graph') resize(); });
async function tick(){ try{ const r=await fetch('/data.json?ts='+Date.now()); DATA=await r.json(); render(); }catch(e){ document.getElementById('st').textContent='fetch error '+e; } }
bindSeq(); resize(); loop(); tick(); setInterval(tick,4000);
</script></body></html>`;
const srv=http.createServer((req,res)=>{ const url=(req.url||'/').split('?')[0];
 if(url==='/data.json'){ const now=Date.now(); if(now-cache.t>2000) cache={t:now,data:build()}; res.writeHead(200,{'content-type':'application/json','cache-control':'no-store'}); res.end(JSON.stringify(cache.data)); return; }
 if(url==='/'||url==='/index.html'){ res.writeHead(200,{'content-type':'text/html; charset=utf-8'}); res.end(html); return; }
 res.writeHead(404); res.end('not found'); });
srv.listen(PORT,'127.0.0.1',()=>console.log('DAG VIZ on http://127.0.0.1:'+PORT));