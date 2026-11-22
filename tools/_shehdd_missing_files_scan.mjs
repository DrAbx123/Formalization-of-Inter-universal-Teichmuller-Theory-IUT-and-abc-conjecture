import { readFileSync, existsSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const files=['dag/target-chain.json'];
for(const f of readdirSync(ROOT+'/coord')){ if(/^target-chain\..+\.json$/.test(f) && f!=='target-chain.TEMPLATE.json') files.push('coord/'+f); }
const actionable=new Set(['NAMED','GAP','CONDITIONAL','DEF']);
let missing=[];
for(const f of files){
  let j; try{ j=JSON.parse(readFileSync(ROOT+'/'+f,'utf8')); }catch{ continue; }
  for(const n of (j.nodes||[])){
    if(!actionable.has(n.status)) continue;
    const fs_=n.files||[];
    const absent=fs_.filter(x=>!existsSync(ROOT+'/'+x));
    if(fs_.length===0 || absent.length>0){ missing.push({frag:f, id:n.id, status:n.status, files:fs_.length, absent:absent.slice(0,3)}); }
  }
}
console.log('actionable nodes with missing/empty files: '+missing.length);
for(const m of missing.slice(0,40)) console.log(m.id+' ['+m.status+'] files='+m.files+' absent='+m.absent.join(','));
