import { readFileSync, writeFileSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const files=['dag/target-chain.json'];
for(const f of readdirSync(ROOT+'/coord')){ if(/^target-chain\..+\.json$/.test(f)&&f!=='target-chain.TEMPLATE.json') files.push('coord/'+f); }
let kinds=0, statuses=0, edges=0, changed=0;
for(const rel of files){
  let j; try{ j=JSON.parse(readFileSync(ROOT+'/'+rel,'utf8')); }catch{ continue; }
  let dirty=false;
  for(const n of (j.nodes||[])){
    if(n.kind==='statement'){ n.kind='theorem'; kinds++; dirty=true; }
    if(n.status==='PENDING-VERIFY'){ n.status='CONDITIONAL'; if(n.note) n.note='PENDING-VERIFY escalated to CONDITIONAL (validator fix by shehdd); '+n.note; statuses++; dirty=true; }
  }
  for(const e of (j.edges||[])){ if(e.kind==='hierarchy'){ e.kind='statement'; edges++; dirty=true; } }
  if(dirty){ writeFileSync(ROOT+'/'+rel, JSON.stringify(j,null,2)); changed++; }
}
console.log('kind_fixed='+kinds+' status_fixed='+statuses+' edges_fixed='+edges+' files='+changed);
