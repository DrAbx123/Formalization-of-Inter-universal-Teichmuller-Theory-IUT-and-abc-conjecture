import { readFileSync, writeFileSync, existsSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const files=['dag/target-chain.json'];
for(const f of readdirSync(ROOT+'/coord')){ if(/^target-chain\..+\.json$/.test(f) && f!=='target-chain.TEMPLATE.json') files.push('coord/'+f); }
const actionable=new Set(['NAMED','GAP','CONDITIONAL','DEF','TREE_ASSET']);
let empty=[];
for(const f of files){
  let j; try{ j=JSON.parse(readFileSync(ROOT+'/'+f,'utf8')); }catch{ continue; }
  for(const n of (j.nodes||[])){
    if(!actionable.has(n.status)) continue;
    const fs_=(n.files||[]);
    if(fs_.length===0) continue;
    const decls=n.declarations||{};
    const hasDecl=Object.values(decls).some(v=>Array.isArray(v)&&v.length>0);
    if(!hasDecl) empty.push({frag:f,id:n.id,status:n.status,files:fs_});
  }
}
console.log('actionable nodes with empty declarations: '+empty.length);
for(const e of empty.slice(0,40)) console.log(e.id+' ['+e.status+'] '+(e.files[0]||''));
