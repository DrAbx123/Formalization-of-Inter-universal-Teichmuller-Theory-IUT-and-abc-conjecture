import { readFileSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const idx=JSON.parse(readFileSync(ROOT+'/dag/generated/declarations-index.json','utf8')).declarations;
for(const t of ['normOneUnits','closedUnitBallUnits','ofFinite','P1Point']){
  const hits=idx.filter(d=>d.name.includes(t) && (d.file.includes('Frobenioid')||d.file.includes('HodgeTheater')||d.file.includes('P1')||d.file.includes('Geometry/AlgebraicClosure')||d.file.includes('ClosedBall'))).slice(0,12);
  console.log('##',t); for(const h of hits) console.log(' ',h.name,'(',h.kind,')',h.file);
}