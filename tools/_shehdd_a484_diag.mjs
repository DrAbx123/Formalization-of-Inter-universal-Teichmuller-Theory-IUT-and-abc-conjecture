import { readFileSync, existsSync, statSync } from 'node:fs';
const ROOT='D:/lean';
const files=['tmp/sheaf/xif/paper/Mzk1R4LiteralAssemblyActual.lean','tmp/sheaf/xif/paper/A483LiteralCarrierProductHaarActual.lean','tmp/sheaf/xif/paper/Mzk1QPilotSHEDoubleImageActual.lean'];
for(const f of files){
  const src=ROOT+'/'+f;
  if(!existsSync(src)){ console.log(f+' MISSING'); continue; }
  const st=statSync(src);
  const txt=readFileSync(src,'utf8');
  const imports=txt.split('\n').filter(l=>l.startsWith('import ')).map(l=>l.slice(7).trim());
  const hasOI=imports.some(i=>i.includes('SourceOriginalInput'));
  console.log(f+' mtime='+st.mtime.toISOString().slice(11,19)+' imports='+imports.length+' hasOriginalInputImport='+hasOI);
}
