import { readFileSync, writeFileSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const files=['dag/target-chain.json'];
for(const f of readdirSync(ROOT+'/coord')){ if(/^target-chain\..+\.json$/.test(f)&&f!=='target-chain.TEMPLATE.json') files.push('coord/'+f); }
let kinds=0,stat=0,edges=0,prefixes=0,changed=0;
for(const rel of files){
  let j; try{ j=JSON.parse(readFileSync(ROOT+'/'+rel,'utf8')); }catch{ continue; }
  let dirty=false;
  for(const n of (j.nodes||[])){
    if(n.kind==='statement'){ n.kind='theorem'; kinds++; dirty=true; }
    if(n.status==='PENDING-VERIFY'){ n.status='CONDITIONAL'; if(n.note) n.note='PENDING-VERIFY escalated to CONDITIONAL (validator fix by shehdd); '+n.note; stat++; dirty=true; }
  }
  for(const e of (j.edges||[])){ if(e.kind==='hierarchy'){ e.kind='statement'; edges++; dirty=true; } }
  if(rel.endsWith('target-chain.iuti-ii.json')){
    for(const n of (j.nodes||[])){ while(n.id && n.id.startsWith('iuti-ii:')){ n.id=n.id.slice('iuti-ii:'.length); dirty=true; prefixes++; } }
    for(const e of (j.edges||[])){ for(const k of ['from','to']){ while(e[k] && e[k].startsWith('iuti-ii:')){ e[k]=e[k].slice('iuti-ii:'.length); dirty=true; prefixes++; } } }
  }
  if(dirty){ writeFileSync(ROOT+'/'+rel, JSON.stringify(j,null,2)); changed++; }
}
console.log('kind='+kinds+' status='+stat+' edge_kind='+edges+' prefix_strips='+prefixes+' files='+changed);
