import { readFileSync } from 'node:fs';
const idx=JSON.parse(readFileSync('D:/lean/dag/generated/declarations-index.json','utf8')).declarations;
const terms=['Cor312Conclusion','qSigned','thetaSigned','StepXIContract','step3115','hullReadout','detReadout','qThetaHullReadout','QThetaDoubleImage'];
for(const t of terms){
  const hits=idx.filter(d=>d.name.includes(t));
  console.log('##',t,'hits',hits.length);
  for(const h of hits.slice(0,25)) console.log(' ',h.kind,h.name,'@',h.file);
}