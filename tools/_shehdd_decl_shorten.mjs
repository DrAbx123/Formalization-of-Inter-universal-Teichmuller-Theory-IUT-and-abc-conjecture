import { readFileSync, writeFileSync, existsSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const files=['dag/target-chain.json'];
for(const f of readdirSync(ROOT+'/coord')){ if(/^target-chain\..+\.json$/.test(f)&&f!=='target-chain.TEMPLATE.json') files.push('coord/'+f); }
let fixed=0, changed=0;
for(const rel of files){
  let j; try{ j=JSON.parse(readFileSync(ROOT+'/'+rel,'utf8')); }catch{ continue; }
  let dirty=false;
  for(const n of (j.nodes||[])){
    for(const [f,names] of Object.entries(n.declarations||{})){
      const fp=ROOT+'/'+f; if(!existsSync(fp)) continue;
      const src=readFileSync(fp,'utf8');
      const out=[];
      for(const name of names){
        let pick=null;
        if(src.includes(name)) pick=name;
        else {
          const parts=name.split('.');
          const last=parts[parts.length-1];
          if(src.includes(last)) pick=last;
          else if(parts.length>=2 && src.includes(parts.slice(-2).join('.'))) pick=parts.slice(-2).join('.');
        }
        if(pick && !out.includes(pick)) out.push(pick);
      }
      if(JSON.stringify(out)!==JSON.stringify(names)){ n.declarations[f]=out; dirty=true; fixed++; }
    }
  }
  if(dirty){ writeFileSync(ROOT+'/'+rel, JSON.stringify(j,null,2)); changed++; }
}
console.log('decl_lists_fixed='+fixed+' files_changed='+changed);
