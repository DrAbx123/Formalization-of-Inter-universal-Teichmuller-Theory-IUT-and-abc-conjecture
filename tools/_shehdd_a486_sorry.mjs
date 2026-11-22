import { readFileSync, existsSync, statSync } from 'node:fs';
const ROOT='D:/lean';
function codeText(s){ let out=''; let i=0; const n=s.length;
  while(i<n){ const c=s[i], c2=s.slice(i,i+2);
    if(c2==='/-'){ let d=1; i+=2; while(i<n&&d>0){ const e=s.slice(i,i+2); if(e==='/ -'){d++;i+=2;} else if(e==='-/'){d--;i+=2;} else i++; } continue; }
    if(c2==='--'){ while(i<n&&s[i]!=='\n') i++; continue; }
    if(c==='"'){ i++; while(i<n&&s[i]!=='"'){ if(s[i]==='\\') i+=2; else i++; } i++; continue; }
    if(c==="'"){ i++; while(i<n&&s[i]!=="'"){ if(s[i]==='\\') i+=2; else i++; } i++; continue; }
    out+=c; i++; }
  return out; }
const files=['Mzk1QPilotR4Stage5AlignActual','Mzk1HullDetStep3115Actual','Mzk1Step3115ComparisonActual','Mzk1Step3115WiringActual','Mzk1R4LiteralAssemblyActual','Mzk1R4LiteralAssemblyV2Actual','Mzk1FourTriangleSynthesisActual','Mzk1HullDetFourTriangleActual','Mzk1R4EndgameCompositionActual'];
for(const n of files){
  const f='tmp/sheaf/xif/paper/'+n+'.lean'; const src=ROOT+'/'+f;
  if(!existsSync(src)){ console.log(n+' NO-SRC'); continue; }
  const txt=readFileSync(src,'utf8');
  const sor=(codeText(txt).match(/\bsorry\b/g)||[]).length;
  const o=ROOT+'/.lake/build/lib/lean/'+f.replace(/\.lean$/,'.olean');
  console.log(n+' | sorries='+sor+' | olean='+(existsSync(o)?statSync(o).mtime.toISOString().slice(11,19):'miss')+' | src='+statSync(src).mtime.toISOString().slice(11,19));
}
