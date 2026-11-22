import { readFileSync, writeFileSync } from 'node:fs';
const ROOT='D:/lean';
for(const f of ['tools/_shehdd_validnotes_repro.mjs','tools/_shehdd_validnotes_write.mjs']){
  try{ let t=readFileSync(ROOT+'/'+f,'utf8'); if(t.includes('dag_merge2')){ t=t.split('dag_merge2').join('dag_merge3'); writeFileSync(ROOT+'/'+f,t); console.log('updated '+f); } }catch{}
}
