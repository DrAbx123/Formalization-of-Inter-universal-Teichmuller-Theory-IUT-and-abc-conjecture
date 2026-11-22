import { readFileSync, writeFileSync, existsSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const declsWithNs=(txt)=>{ const out=[]; const stack=[]; const FQN=()=>stack.filter(s=>s.kind==='ns').map(s=>s.name).join('.');
  for(const raw of txt.split('\n')){ const line=raw.trim();
    if(line.startsWith('--')) continue;
    const mNs=line.match(/^namespace\s+([A-Za-z0-9_.']+)\s*$/); if(mNs){ stack.push({kind:'ns',name:mNs[1]}); continue; }
    if(/^(?:noncomputable\s+)?section\b/.test(line)){ stack.push({kind:'sec'}); continue; }
    if(/^end(\s+[A-Za-z0-9_.']+)?\s*$/.test(line)){ if(stack.length) stack.pop(); continue; }
    const m=line.match(/^(?:theorem|lemma|def|abbrev|structure|inductive)\s+([A-Za-z0-9_'.]+)/);
    if(m){ const ns=FQN(); out.push(ns? ns+'.'+m[1] : m[1]); }
  } return out; };
const files=['dag/target-chain.json'];
for(const f of readdirSync(ROOT+'/coord')){ if(/^target-chain\..+\.json$/.test(f)&&f!=='target-chain.TEMPLATE.json') files.push('coord/'+f); }
let fixedNodes=0, changedFiles=0;
for(const rel of files){
  let j; try{ j=JSON.parse(readFileSync(ROOT+'/'+rel,'utf8')); }catch{ continue; }
  let dirty=false;
  for(const n of (j.nodes||[])){
    const declMap=n.declarations||{};
    for(const [f,names] of Object.entries(declMap)){
      const fp=ROOT+'/'+f;
      if(!existsSync(fp)) continue;
      const src=readFileSync(fp,'utf8');
      const stale=names.filter(x=>!src.includes(x));
      if(!stale.length) continue;
      const actual=declsWithNs(src);
      const keep=names.filter(x=>src.includes(x));
      const add=actual.filter(x=>!keep.includes(x));
      const merged=keep.concat(add).slice(0,30);
      if(merged.length!==names.length){ declMap[f]=merged; dirty=true; fixedNodes++; }
    }
  }
  // iuti-ii double-prefix fix
  if(rel.endsWith('target-chain.iuti-ii.json')){
    for(const n of (j.nodes||[])){ while(n.id && n.id.startsWith('iuti-ii:')) n.id=n.id.slice('iuti-ii:'.length); }
    for(const e of (j.edges||[])){ for(const k of ['from','to']){ while(e[k] && e[k].startsWith('iuti-ii:')) e[k]=e[k].slice('iuti-ii:'.length); } }
    dirty=true;
  }
  if(dirty){ writeFileSync(ROOT+'/'+rel, JSON.stringify(j,null,2)); changedFiles++; }
}
console.log('files_changed='+changedFiles+' decl_maps_fixed='+fixedNodes);
