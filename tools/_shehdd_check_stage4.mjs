import { readFileSync } from 'node:fs';
const ROOT='D:/lean';
const j=JSON.parse(readFileSync(ROOT+'/coord/target-chain.iut-pre-stage4.json','utf8'));
console.log('nodes='+j.nodes.length);
for(const n of j.nodes) console.log(n.id+' ['+n.status+']');
