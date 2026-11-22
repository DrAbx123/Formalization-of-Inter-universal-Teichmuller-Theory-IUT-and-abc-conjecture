import { readFileSync } from 'node:fs';
const ROOT='D:/lean';
const d=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
console.log('node keys sample='+JSON.stringify(Object.keys(d.nodes[0])));
console.log(JSON.stringify(d.nodes.find(n=>n.id&&n.id.startsWith('shehdd:'))||{}).slice(0,600));
console.log('edge keys='+JSON.stringify(Object.keys(d.edges[0])));
