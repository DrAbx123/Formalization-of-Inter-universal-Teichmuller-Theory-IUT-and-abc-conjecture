import { readFileSync } from 'node:fs';
const ROOT='D:/lean';
const idx=JSON.parse(readFileSync(ROOT+'/dag/generated/declarations-index.json','utf8')).declarations;
const hits=idx.filter(d=>d.name.includes('ofFinite')||d.name.includes('infty')||d.name.includes('inity')).filter(d=>d.file.includes('P1')||d.file.includes('StepProvider')||d.file.includes('Measure'));
console.log('count',hits.length);
for(const h of hits.slice(0,40)) console.log(h.name,'(',h.kind,')',h.file);