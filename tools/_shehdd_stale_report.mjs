import { readFileSync, existsSync, statSync } from 'node:fs';
const ROOT='D:/lean';
const d=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const declsWithNs=(txt)=>{ const out=[]; const stack=[]; const FQN=()=>stack.filter(s=>s.kind==='ns').map(s=>s.name).join('.');
  for(const raw of txt.split('\n')){ const line=raw.trim();
    const mNs=line.match(/^namespace\s+([A-Za-z0-9_.'+]+)\s*$/); if(mNs){ stack.push({kind:'ns',name:mNs[1]}); continue; }
    if(/^(?:noncomputable\s+)?section\b/.test(line)){ stack.push({kind:'sec'}); continue; }
    if(/^end(\s+[A-Za-z0-9_.'+]+)?\s*$/.test(line)){ if(stack.length) stack.pop(); continue; }
    const m=line.match(/^(?:theorem|lemma|def|abbrev|structure|inductive)\s+([A-Za-z0-9_'.]+)/);
    if(m){ const ns=FQN(); out.push(ns? ns+'.'+m[1] : m[1]); }
  } return out; };
const stale=new Map();
for(const n of d.nodes){ for(const [f,decls] of Object.entries(n.declarations||{})){ const fp=ROOT+'/'+f; if(!existsSync(fp)) continue; const src=readFileSync(fp,'utf8'); for(const name of decls){ if(!src.includes(name)){ if(!stale.has(f)) stale.set(f,[]); stale.get(f).push({node:n.id,name}); } } } }
for(const [f,items] of stale){
  const mt=statSync(ROOT+'/'+f).mtime.toISOString();
  const actual=declsWithNs(readFileSync(ROOT+'/'+f,'utf8'));
  console.log('=== '+f+' mtime='+mt+' stale='+items.length+' actual='+actual.length);
  console.log('  stale: '+items.map(x=>x.name).slice(0,6).join(', '));
  console.log('  actual sample: '+actual.slice(0,8).join(', '));
}
