import { readFileSync } from 'node:fs';
const txt=readFileSync('D:/lean/tmp/sheaf/xif/paper/IUTExternal20ProofStatusActual.lean','utf8');
const declsWithNs=(txt)=>{ const out=[]; const stack=[]; const FQN=()=>stack.filter(s=>s.kind==='ns').map(s=>s.name).join('.');
  for(const raw of txt.split('\n')){ const line=raw.trim();
    const mNs=line.match(/^namespace\s+([A-Za-z0-9_.']+)\s*$/);
    if(mNs){ stack.push({kind:'ns',name:mNs[1]}); continue; }
    if(/^(?:noncomputable\s+)?section\b/.test(line)){ stack.push({kind:'sec'}); continue; }
    if(/^end(\s+[A-Za-z0-9_.']+)?\s*$/.test(line)){ if(stack.length) stack.pop(); continue; }
    const m=line.match(/^(?:theorem|lemma|def|abbrev)\s+([A-Za-z0-9_'.]+)/);
    if(m){ const ns=FQN(); out.push(ns? ns+'.'+m[1] : m[1]); }
  } return out; };
console.log(declsWithNs(txt));
