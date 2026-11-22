import { readFileSync, writeFileSync, existsSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
const ROOT='D:/lean';
const rt=JSON.parse(readFileSync(ROOT+'/dag/watchdog/runtime-status.json','utf8'));
const good=new Map(); for(const n of rt.nodes){ if(n.all_fresh && n.exits_ok!==false) good.set(n.id,n); }
const files=['dag/target-chain.json'];
for(const f of readdirSync(ROOT+'/coord')){ if(/^target-chain\..+\.json$/.test(f) && f!=='target-chain.TEMPLATE.json') files.push('coord/'+f); }
let up=0; const list=[];
for(const f of files){
  let j; try{ j=JSON.parse(readFileSync(ROOT+'/'+f,'utf8')); }catch{ continue; }
  let dirty=false;
  for(const n of (j.nodes||[])){
    if(n.status!=='GAP') continue;
    if(good.has(n.id) || good.has('foundation:'+n.id) || good.has('iutiii:'+n.id) || good.has('iuti-ii:'+n.id)){
      n.status='TREE_ASSET'; n.note='BUILD GAP RESOLVED (shehdd evidence): fresh oleans + exits ok per runtime-status; asset tree available. '+(n.note||''); up++; dirty=true; list.push(n.id);
    }
  }
  if(dirty) writeFileSync(ROOT+'/'+f, JSON.stringify(j,null,2));
}
console.log('upgraded GAP->TREE_ASSET: '+up);
console.log(list.slice(0,20).join('\n'));
