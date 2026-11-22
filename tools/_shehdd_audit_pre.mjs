import { readFileSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const j=JSON.parse(readFileSync(ROOT+'/coord/target-chain.iut-pre-abc.json','utf8'));
console.log('keys='+Object.keys(j).join(','));
console.log('nodes='+(j.nodes||[]).length+' edges='+(j.edges||[]).length);
const nk={}, ns={}, ek={}, ev={};
for(const n of (j.nodes||[])){ nk[n.kind]=(nk[n.kind]||0)+1; ns[n.status]=(ns[n.status]||0)+1; }
for(const e of (j.edges||[])){ ek[e.kind]=(ek[e.kind]||0)+1; ev[e.evidence]=(ev[e.evidence]||0)+1; }
console.log('node kinds='+JSON.stringify(nk)); console.log('statuses='+JSON.stringify(ns));
console.log('edge kinds='+JSON.stringify(ek)); console.log('evidence='+JSON.stringify(ev));
console.log('--- first 3 nodes ---'); for(const n of (j.nodes||[]).slice(0,3)) console.log(JSON.stringify(n,null,1));
console.log('--- first 3 edges ---'); for(const e of (j.edges||[]).slice(0,3)) console.log(JSON.stringify(e,null,1));
