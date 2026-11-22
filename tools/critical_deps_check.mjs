import { readFileSync, existsSync } from 'node:fs';
import { join } from 'node:path';
const ROOT='D:/lean';
const prio=readFileSync(join(ROOT,'dag/watchdog/priority-files.txt'),'utf8').split(/\r?\n/).filter(Boolean);
const extras=new Set(readFileSync(join(ROOT,'dag/watchdog/extra-targets.txt'),'utf8').split(/\r?\n/).filter(Boolean));
const oleanOf=(f)=>{ const m=f.replace(/\.lean$/,''); return existsSync(join(ROOT,'.lake/build/lib/lean',m+'.olean'))||existsSync(join(ROOT,'.lean-shadow/project',m+'.olean')); };
const resolve=(mod)=>{ const rel=mod.replaceAll('.','/')+'.lean'; for(const base of ['', 'tmp/external/ported/']) { const p=base+rel; if(existsSync(join(ROOT,p))) return p; } const ported=mod.split('.')[0]; const rest=mod.split('.').slice(1).join('/')+'.lean'; const p2='tmp/external/ported/'+ported+'/'+rest; if(existsSync(join(ROOT,p2))) return p2; return null; };
const importRe=/^\s*import\s+([A-Za-z0-9_.']+)/gm;
const missing=new Set(); const queue=[]; const seen=new Set();
for(const p of prio) queue.push(p);
while(queue.length){ const f=queue.pop(); if(seen.has(f)) continue; seen.add(f); let s=''; try{ s=readFileSync(join(ROOT,f),'utf8'); }catch{ continue; } let m; importRe.lastIndex=0; const imps=[]; while((m=importRe.exec(s))) imps.push(m[1]); for(const im of imps){ const dep=resolve(im); if(!dep) continue; if(oleanOf(dep)) continue; if(extras.has(dep)) continue; missing.add(dep); if(missing.size<300) queue.push(dep); } }
console.log(JSON.stringify({priority:prio.length, missing_deps:[...missing]},null,1));