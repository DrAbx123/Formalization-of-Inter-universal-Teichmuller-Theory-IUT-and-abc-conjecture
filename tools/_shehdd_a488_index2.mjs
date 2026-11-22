import { readFileSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const idx=JSON.parse(readFileSync(ROOT+'/dag/generated/declarations-index.json','utf8')).declarations;
const pats=[/logDiff/i,/logCond/i,/kappaLog/i,/kappa_log/i,/excBound/i,/552960/,/1\.464/,/4\.088/,/szpiro/i,/Szpiro/i,/ABCHeight/i,/abcHeight/i];
for(const p of pats){
  const hits=idx.filter(d=>p.test(d.name));
  console.log('PATTERN '+p+' decls='+hits.length);
  for(const h of hits.slice(0,10)) console.log('  '+h.name+' @ '+h.file);
}
