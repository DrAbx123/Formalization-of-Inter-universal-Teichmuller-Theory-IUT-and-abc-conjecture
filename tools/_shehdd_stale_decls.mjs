import { readFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const d=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const out=[];
for(const n of d.nodes){
  for(const [f,decls] of Object.entries(n.declarations||{})){
    const fp=ROOT+'/'+f; if(!existsSync(fp)){ out.push({node:n.id,file:f,kind:'missing-file'}); continue; }
    const src=readFileSync(fp,'utf8');
    for(const name of decls){ if(!src.includes(name)) out.push({node:n.id,file:f,decl:name}); }
  }
}
const byNode={};
for(const o of out){ byNode[o.node]=(byNode[o.node]||0)+1; }
console.log('total stale decls='+out.length+' affected nodes='+Object.keys(byNode).length);
for(const [k,v] of Object.entries(byNode).slice(0,25)) console.log(v+'	'+k);
