import { readFileSync } from 'node:fs';
const ROOT='D:/lean';
const b=JSON.parse(readFileSync(ROOT+'/coord/DAG-BLOCKED.json','utf8')).blocked||[];
const d=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const byId=new Map(d.nodes.map(n=>[n.id,n]));
console.log('blocked='+b.length);
for(const x of b){
  const n=byId.get(x.id);
  console.log((n? n.status : 'MISSING')+' | '+x.id+' | '+(x.kind||'')+' | '+(x.reason||'').slice(0,90));
}
