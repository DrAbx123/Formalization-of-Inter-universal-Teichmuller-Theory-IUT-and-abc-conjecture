import { readFileSync, writeFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
for(const e of j.edges){ if(e.from==='abc-logbound-form'&&e.to==='T6-abc-log-form'){ e.to='mainline:abc-log-equivalence'; } }
j.nodes.find(n=>n.id==='abc-logbound-form').note+=' Edge adjusted: T6-abc-log-form node absent in merged DAG; hangs on existing mainline:abc-log-equivalence.';
writeFileSync(p, JSON.stringify(j,null,2));
console.log('edge fixed');
