import { readFileSync, writeFileSync, existsSync, openSync, closeSync, unlinkSync, renameSync } from 'node:fs';
import { join } from 'node:path';
const ROOT='D:/lean'; const PATH=join(ROOT,'dag','watchdog','extra-targets.txt'); const LOCK=join(ROOT,'dag','watchdog','.extras.lock');
let fd=null; for(let i=0;i<120;i++){ try{ fd=openSync(LOCK,'wx'); break; }catch{ await new Promise(r=>setTimeout(r,250)); } }
const read=()=>{ const raw=readFileSync(PATH,'utf8'); let lines=raw.split(/\r?\n/).map(s=>s.trim()).filter(Boolean);
  const out=[]; for(const l of lines){ if(l.endsWith('.lean')) out.push(l); else { const parts=l.split(/(?<=\.lean)(?=\S)/); for(const p of parts) if(p.endsWith('.lean')) out.push(p); } } return out; };
const args=process.argv.slice(2);
const lines=read(); const set=new Set(lines); let added=0, missing=[];
for(const a of args){ const p=a.replaceAll('\\','/').replace(/^\.\//,''); if(!p.endsWith('.lean')) continue; if(!existsSync(join(ROOT,p))){ missing.push(p); continue; } if(!set.has(p)){ set.add(p); lines.push(p); added++; } }
const tmp=PATH+'.tmp'; writeFileSync(tmp, lines.join('\n')+'\n'); renameSync(tmp,PATH);
if(fd!==null){ try{ closeSync(fd); }catch{} try{ unlinkSync(LOCK); }catch{} }
console.log(JSON.stringify({total:lines.length,added,missing},null,1));