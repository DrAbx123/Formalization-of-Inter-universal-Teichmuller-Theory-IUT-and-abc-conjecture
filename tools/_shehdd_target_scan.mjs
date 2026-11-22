import { readFileSync } from 'node:fs';
const ROOT='D:/lean';
const idx=JSON.parse(readFileSync(ROOT+'/dag/generated/declarations-index.json','utf8')).declarations;
const pats=[/paperScopeLemma24Target|PaperScopeLemma24Target/i,/numMaxP/i,/f0StepTarget|f0CritValue|f0Map/i,/stepSet|stepProvider/i];
for(const re of pats){ const hits=idx.filter(d=>re.test(d.name)); console.log('/'+re.source+'/ hits='+hits.length); for(const h of hits.slice(0,14)) console.log('  '+h.name+' | '+h.file+':'+(h.line||'')); }
