import { readFileSync, writeFileSync, existsSync, openSync, closeSync, unlinkSync, renameSync } from 'node:fs';
import { join } from 'node:path';
const ROOT='D:/lean'; const PATH=join(ROOT,'dag/watchdog/extra-targets.txt'); const LOCK=join(ROOT,'dag/watchdog','.extras.lock');
let fd=null; for(let i=0;i<240;i++){ try{ fd=openSync(LOCK,'wx'); break; }catch{ await new Promise(r=>setTimeout(r,250)); } }
const list=readFileSync(process.argv[2],'utf8').split(/\r?\n/).filter(Boolean).map(s=>s.trim()).filter(p=>p.endsWith('.lean'));
const raw=readFileSync(PATH,'utf8').split(/\r?\n/).filter(Boolean); const set=new Set(raw); let added=0, missing=[];
for(const p of list){ if(!existsSync(join(ROOT,p))){ missing.push(p); continue; } if(!set.has(p)){ set.add(p); raw.push(p); added++; } }
const tmp=PATH+'.tmp'; writeFileSync(tmp, raw.join('\n')+'\n'); renameSync(tmp,PATH);
if(fd!==null){ try{ closeSync(fd); }catch{} try{ unlinkSync(LOCK); }catch{} }
console.log(JSON.stringify({total:raw.length,added,missing:missing.length},null,1));