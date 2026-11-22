import { readFileSync, writeFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
for(const e of j.edges){ if(e.from==='geomcore-route-consumer'&&e.to==='iut-pre-stage4:D.witness.precise'){ e.to='foundation:D.bridgeLegacy'; } }
j.nodes.find(n=>n.id==='geomcore-route-consumer').note += ' Edge adjusted after owner rewrite of iut-pre-stage4 fragment (D.witness.precise removed): consumer now hangs on foundation:D.bridgeLegacy (existing PROVED bridge-legacy node).';
writeFileSync(p, JSON.stringify(j,null,2));
console.log('edge fixed');
