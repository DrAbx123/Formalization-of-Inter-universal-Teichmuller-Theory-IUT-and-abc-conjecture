import { readFileSync, existsSync, statSync } from 'node:fs';
const ROOT='D:/lean';
const next=JSON.parse(readFileSync(ROOT+'/dag/watchdog/next.json','utf8'));
let i=0;
for(const n of next.top.slice(0,80)){
  i++;
  let mt='-';
  const f=(n.files||[])[0];
  if(f && existsSync(ROOT+'/'+f)){ const s=statSync(ROOT+'/'+f); mt=new Date(s.mtimeMs).toISOString().slice(11,19); }
  console.log(i+' | '+n.id+' | '+n.kind+' | '+n.status+' | d='+n.unproved_deps+' | '+mt+' | '+((n.files||[])[0]||''));
}
