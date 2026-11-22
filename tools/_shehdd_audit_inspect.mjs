import { readFileSync } from 'node:fs';
const ROOT='D:/lean';
const j=JSON.parse(readFileSync(ROOT+'/coord/target-chain.iut-skeleton.json','utf8'));
console.log('top keys='+Object.keys(j).join(','));
console.log('nodes='+(j.nodes||[]).length+' edges='+(j.edges||[]).length);
console.log('--- node sample ---');
for(const n of (j.nodes||[]).slice(0,3)) console.log(JSON.stringify(n,null,1));
console.log('--- edge sample ---');
for(const e of (j.edges||[]).slice(0,5)) console.log(JSON.stringify(e,null,1));
