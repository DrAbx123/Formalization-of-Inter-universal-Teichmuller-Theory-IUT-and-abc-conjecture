import { readFileSync } from 'node:fs';
const ROOT='D:/lean';
const idx=JSON.parse(readFileSync(ROOT+'/dag/generated/declarations-index.json','utf8'));
console.log(Object.keys(idx));
const decls=idx.declarations||idx;
console.log('len='+decls.length);
console.log(JSON.stringify(decls[0]));
console.log(JSON.stringify(decls[500]));
