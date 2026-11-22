import { readFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const prio=readFileSync(ROOT+'/dag/watchdog/priority-files.txt','utf8').split('\n').filter(Boolean);
const olean=f=>existsSync(ROOT+'/.lake/build/lib/lean/'+f.replace(/\.lean$/,'.olean'));
function codeText(s){ let out=''; let i=0; const n=s.length;
  while(i<n){ const c=s[i], c2=s.slice(i,i+2);
    if(c2==='/-'){ let d=1; i+=2; while(i<n&&d>0){ const e=s.slice(i,i+2); if(e==='/-'){d++;i+=2;} else if(e==='-/'){d--;i+=2;} else i++; } continue; }
    if(c2==='--'){ while(i<n&&s[i]!=='\n') i++; continue; }
    if(c==='"'){ i++; while(i<n&&s[i]!=='"'){ if(s[i]==='\\') i+=2; else i++; } i++; continue; }
    if(c==="'"){ if(i+2<n && (s[i+2]==="'" || (s[i+1]==='\\'&&i+3<n&&s[i+3]==="'"))){ i++; while(i<n&&s[i]!=="'"){ if(s[i]==='\\') i+=2; else i++; } i++; continue; } out+=c;i++;continue; }
    out+=c; i++; }
  return out; }
console.log('priority='+prio.length+' green='+prio.filter(olean).length);
for(const f of prio){
  if(!existsSync(ROOT+'/'+f)){ console.log('NOSRC '+f); continue; }
  const txt=readFileSync(ROOT+'/'+f,'utf8');
  const real=(codeText(txt).match(/\bsorry\b/g)||[]).length;
  const green=olean(f);
  if(real>0||!green) console.log((green?'GREEN':'MISS ')+' sorries='+real+' '+f);
}
