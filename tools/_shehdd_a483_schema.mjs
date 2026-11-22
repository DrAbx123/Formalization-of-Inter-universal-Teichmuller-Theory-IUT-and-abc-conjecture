import { readFileSync } from 'node:fs';
const ROOT='D:/lean';
const j=JSON.parse(readFileSync(ROOT+'/dag/GAP-CLOSURE-CANDIDATES.json','utf8'));
console.log('top keys='+JSON.stringify(Object.keys(j)).slice(0,800));
const items=Array.isArray(j)?j:(j.gaps||j.candidates||j.groups||j.results);
if(Array.isArray(items)){ console.log('gaps count='+items.length); for(const g of items){ const keys=Object.keys(g); console.log('GAP '+(g.id||g.gap||g.name||g.title||JSON.stringify(Object.keys(g)).slice(0,120))+' : '+keys.join(',')); } }
else { for(const [k,v] of Object.entries(j)){ console.log('KEY '+k+' type='+(Array.isArray(v)?('array '+v.length):typeof v)); } }
