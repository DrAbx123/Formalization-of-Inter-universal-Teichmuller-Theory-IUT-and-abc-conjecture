import { readFileSync } from 'node:fs';
const ROOT='D:/lean';
const j=JSON.parse(readFileSync(ROOT+'/dag/GAP-CLOSURE-CANDIDATES.json','utf8'));
for(const name of ['scheme_side','fiber_functor','qpilot','iut4_compare']){
  const g=j.groups[name];
  console.log('=== '+name+' SUMMARY '+JSON.stringify(g.summary));
  for(const d of (g.decl_sample||[]).slice(0,20)) console.log('  '+d.name+' | '+d.file);
}
