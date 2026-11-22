import { readFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
for(const f of ['tmp/sheaf/xif/paper/Mzk1Step3115WiringActual.lean','tmp/sheaf/xif/paper/Mzk1HullDetFourTriangleActual.lean']){
  console.log('===== '+f);
  const t=readFileSync(ROOT+'/'+f,'utf8').split('\n');
  for(let i=0;i<t.length;i++){ const s=t[i];
    if(s.startsWith('import ')||s.startsWith('open ')||s.startsWith('namespace ')) console.log('  '+s.trim());
    else if(/^(theorem|def|structure|abbrev) /.test(s)){ let acc=s.trim(); let j=i+1; while(j<t.length&&j<i+16&&!/:=|where/.test(t[j])){ acc+=' '+t[j].trim(); j++; } console.log('  L'+(i+1)+': '+acc.slice(0,330)); } }
  const log=ROOT+'/dag/watchdog/logs/'+f.replace(/\//g,'_')+'.log';
  if(existsSync(log)){ const e=readFileSync(log,'utf8').split('\n').filter(l=>l.includes(': error')).slice(0,3); console.log('  LOG errs='+e.length); e.forEach(x=>console.log('    '+x.trim().slice(0,190))); } else console.log('  no log');
}
