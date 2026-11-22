import { readFileSync } from 'node:fs';
const ROOT='D:/lean';
const idx=JSON.parse(readFileSync(ROOT+'/dag/generated/declarations-index.json','utf8')).declarations;
const pats=[/f4b|numMaxStrict|NumMax/i,/fixedBeta|FixedBeta/i,/StepProvider/i,/problemDApplic|schemeSideMap/i];
for(const re of pats){ const hits=idx.filter(d=>re.test(d.name)||re.test(d.file||'')); console.log('/'+re.source+'/ hits='+hits.length); for(const h of hits.slice(0,10)) console.log('  '+h.name+' | '+h.file+':'+(h.line||'')); }
