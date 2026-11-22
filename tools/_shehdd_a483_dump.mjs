import { readFileSync } from 'node:fs';
const ROOT='D:/lean';
const j=JSON.parse(readFileSync(ROOT+'/dag/GAP-CLOSURE-CANDIDATES.json','utf8'));
for(const [name,g] of Object.entries(j.groups)){
  console.log('=== '+name);
  console.log('SUMMARY '+JSON.stringify(g.summary));
  console.log('DECLS:');
  for(const d of (g.decl_sample||[]).slice(0,25)) console.log('  '+d.name+' | '+d.file);
  console.log('FILES_NO_OLEAN: '+(g.files_no_olean||[]).slice(0,10).join(' ; '));
}
