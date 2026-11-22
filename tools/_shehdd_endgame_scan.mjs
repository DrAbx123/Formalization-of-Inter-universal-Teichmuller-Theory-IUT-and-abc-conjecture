import { readFileSync } from 'node:fs';
const ROOT='D:/lean';
const idx=JSON.parse(readFileSync(ROOT+'/dag/generated/declarations-index.json','utf8')).declarations;
const hits=idx.filter(d=>/endgame/i.test(d.name)||/endgame/i.test(d.file||''));
console.log('endgame decl file hits='+hits.length);
for(const h of hits.slice(0,25)) console.log('  '+h.name+' | '+h.file+':'+(h.line||''));
const a=readFileSync(ROOT+'/coord/ACTUAL-TARGETS.md','utf8');
const rows=a.split('\n').filter(l=>/endgame|gap.*field|two.*gap/i.test(l));
console.log('ACTUAL-TARGETS rows='+rows.length); for(const r of rows.slice(0,15)) console.log('  '+r.slice(0,220));
