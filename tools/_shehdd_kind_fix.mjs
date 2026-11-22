import { readFileSync, writeFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.routes.json';
const j=JSON.parse(readFileSync(p,'utf8'));
let n=0;
for(const node of (j.nodes||[])){ if(node.kind==='statement'){ node.kind='theorem'; n++; } }
if(n) writeFileSync(p, JSON.stringify(j,null,2));
console.log('fixed='+n);
