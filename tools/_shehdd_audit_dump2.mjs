import { readFileSync } from 'node:fs';
const ROOT='D:/lean';
for(const f of ['target-chain.iut-skeleton.json','target-chain.iut-pre-stage4.json','target-chain.iut-pre-mainline.json'])
{ const j=JSON.parse(readFileSync(ROOT+'/coord/'+f,'utf8')); console.log('\n### '+f+' ('+(j.nodes||[]).length+' nodes)'); for(const n of (j.nodes||[])) console.log(n.id+' | '+n.kind+' | '+n.status+' | files='+((n.files||[]).length)+' | '+(n.title||'').slice(0,70)); }
