import { readFileSync } from 'node:fs';
const ROOT='D:/lean';
const rows=JSON.parse(readFileSync(ROOT+'/tmp/_survey_rows.json','utf8'));
const seen=new Set();
for(const r of rows){
  if(!r.decls) continue;
  const ds=r.decls.slice(0,3).map(d=>{ const f=(d.file||'').split('/').pop(); return f+':'+(d.decl||''); });
  for(const d of ds) if(!seen.has(d)){ seen.add(d); }
}
console.log('distinct decl refs='+seen.size);
for(const d of [...seen].slice(0,70)) console.log(d);
