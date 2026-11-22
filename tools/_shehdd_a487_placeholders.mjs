import { readFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const files=[
 'tmp/sheaf/xif/paper/Mzk1FourTriangleSharedActual.lean',
 'tmp/sheaf/xif/paper/Mzk1R4LiteralAssemblyActual.lean',
 'tmp/sheaf/xif/paper/Mzk1Step3115ComparisonActual.lean',
 'tmp/sheaf/xif/paper/Mzk1Step3115WiringActual.lean',
 'tmp/sheaf/xif/paper/Mzk1HullDetStep3115Actual.lean',
 'tmp/sheaf/xif/paper/Mzk1HullDetFourTriangleActual.lean',
 'tmp/sheaf/xif/paper/Mzk1QPilotR4Stage5AlignActual.lean'
];
function codeText(s){ let out=''; let i=0; const n=s.length;
  while(i<n){ const c=s[i], c2=s.slice(i,i+2);
    if(c2==='/-'){ let d=1; i+=2; while(i<n&&d>0){ const e=s.slice(i,i+2); if(e==='/ -'){d++;i+=2;} else if(e==='-/'){d--;i+=2;} else i++; } continue; }
    if(c2==='--'){ while(i<n&&s[i]!=='\n') i++; continue; }
    if(c==='"'){ i++; while(i<n&&s[i]!=='"'){ if(s[i]==='\\') i+=2; else i++; } i++; continue; }
    if(c==="'"){ i++; while(i<n&&s[i]!=="'"){ if(s[i]==='\\') i+=2; else i++; } i++; continue; }
    out+=c; i++; }
  return out; }
for(const f of files){
  const p=ROOT+'/'+f;
  if(!existsSync(p)){ console.log(f.split('/').pop()+' NO-SRC'); continue; }
  const t=readFileSync(p,'utf8'); const code=codeText(t);
  const lines=t.split('\n');
  const hits=[];
  for(let i=0;i<lines.length;i++){ const s=lines[i];
    if(/\bTrue\b/.test(s) && !s.trim().startsWith('--') && !s.includes('/-')) hits.push('L'+(i+1)+' True: '+s.trim().slice(0,110));
    if(/\btrivial\b/.test(s) && !s.trim().startsWith('--')) hits.push('L'+(i+1)+' trivial: '+s.trim().slice(0,110));
  }
  console.log('== '+f.split('/').pop()+' placeholders='+hits.length);
  for(const h of hits.slice(0,6)) console.log('   '+h);
}
console.log('=== Shared decls ===');
const sp=ROOT+'/tmp/sheaf/xif/paper/Mzk1FourTriangleSharedActual.lean';
if(existsSync(sp)){ const t=readFileSync(sp,'utf8').split('\n'); for(let i=0;i<t.length;i++){ if(/^(structure|theorem|def|abbrev) /.test(t[i])){ let s=t[i].trim(); let j=i+1; while(j<t.length&&j<i+14&&!/:=|where/.test(t[j])){ s+=' '+t[j].trim(); j++; } console.log('  L'+(i+1)+': '+s.slice(0,300)); } } }
