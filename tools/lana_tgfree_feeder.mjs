
import { readFileSync, writeFileSync, existsSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const waveFile=ROOT+'/tmp/lana_tgfree_waves.json';
const extra=ROOT+'/dag/watchdog/extra-targets.txt';
const stateFile=ROOT+'/tmp/lana_tgfree_feeder_state.json';
const waves=JSON.parse(readFileSync(waveFile,'utf8')).waves;
let state={next:1};
try{ state=JSON.parse(readFileSync(stateFile,'utf8')); }catch{}
const oleanExists=(f)=>{ const rel=f.replace(/\.lean$/,''); return existsSync(ROOT+'/.lake/build/lib/lean/'+rel+'.olean'); };
const importRe=/^\s*import\s+([A-Za-z0-9_.']+)/gm;
for(let w=state.next; w<waves.length; w++){
  const files=waves[w];
  const depOk=(f)=>{ let s=''; try{ s=readFileSync(ROOT+'/'+f,'utf8'); }catch{ return false; } let mm; importRe.lastIndex=0; let ok=true; while((mm=importRe.exec(s))){ const im=mm[1]; if(im.startsWith('Mathlib')||im.startsWith('Lean')||im.startsWith('Std')) continue; if(im.startsWith('tmp.external.ported.lana_tgfree.')){ const rel=im.replaceAll('.','/')+'.lean'; if(!oleanExists(rel)) ok=false; } else { const rel=im.replaceAll('.','/')+'.lean'; if(!oleanExists(rel)) ok=false; } } return ok; };
  const ready=files.filter(depOk);
  if(ready.length===0){ console.log('waiting at wave',w); break; }
  let cur=new Set(readFileSync(extra,'utf8').split(/\r?\n/).map(x=>x.trim()).filter(Boolean));
  const add=ready.filter(f=>!cur.has(f));
  if(add.length){ appendFileSync(extra, add.map(x=>x+'\n').join('')); console.log('added wave',w,add.length); }
  if(ready.length<files.length){ state.next=w; break; }
  state.next=w+1;
}
writeFileSync(stateFile,JSON.stringify(state));
