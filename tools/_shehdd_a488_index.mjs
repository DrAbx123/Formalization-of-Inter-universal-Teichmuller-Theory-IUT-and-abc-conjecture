import { readFileSync, readdirSync, existsSync } from 'node:fs';
import { join } from 'node:path';
const ROOT='D:/lean';
const idx=JSON.parse(readFileSync(ROOT+'/dag/generated/declarations-index.json','utf8')).declarations;
const pats=[/explicitEstimates/i,/ExpEst/,/ChebyshevExplicit/,/Chebyshev/];
for(const p of pats){
  const hits=idx.filter(d=>p.test(d.name)||(d.file&&p.test(d.file)));
  console.log('PATTERN '+p+' hits='+hits.length);
  for(const h of hits.slice(0,12)) console.log('  '+h.name+' @ '+h.file);
}
