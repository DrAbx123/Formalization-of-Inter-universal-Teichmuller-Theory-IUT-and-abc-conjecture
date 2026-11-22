import { readFileSync, writeFileSync, existsSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const PAPER=ROOT+'/tmp/sheaf/xif/paper';
const lines=readFileSync(ROOT+'/tmp/xif_guarded_results.log','utf8').split('\n');
const latest=(rel)=>{ for(let i=lines.length-1;i>=0;i--){ if(lines[i].includes('FILE='+rel)) return lines[i]; } return null; };
const stripComments=(txt)=>{ const out=[]; let depth=0; for(const raw of txt.split('\n')){
  let line=raw; let res=''; let i=0;
  while(i<line.length){
    if(depth===0){ if(line.startsWith('/-',i)){ depth=1; i+=2; continue; } if(line.startsWith('--',i)){ break; } res+=line[i]; i++; }
    else { if(line.startsWith('/-',i)){ depth++; i+=2; continue; } if(line.startsWith('-/',i)){ depth--; i+=2; continue; } i++; }
  }
  out.push(res);
 } return out.join('\n'); };
const declsWithNs=(txtRaw)=>{ const txt=stripComments(txtRaw); const out=[]; const stack=[]; const FQN=()=>stack.filter(s=>s.kind==='ns').map(s=>s.name).join('.');
  for(const raw of txt.split('\n')){ const line=raw.trim(); if(!line) continue;
    const mNs=line.match(/^namespace\s+([A-Za-z0-9_.']+)\s*$/); if(mNs){ stack.push({kind:'ns',name:mNs[1]}); continue; }
    if(/^(?:noncomputable\s+)?section\b/.test(line)){ stack.push({kind:'sec'}); continue; }
    if(/^end(\s+[A-Za-z0-9_.']+)?\s*$/.test(line)){ if(stack.length) stack.pop(); continue; }
    const m=line.match(/^(?:theorem|lemma|def|abbrev|structure|inductive)\s+([A-Za-z0-9_']+(?:\.[A-Za-z0-9_']+)*)(?=\s|$)/);
    if(m){ const ns=FQN(); out.push(ns? ns+'.'+m[1] : m[1]); }
  } return out; };
let fixed=0;
for(const f of readdirSync(PAPER).filter(f=>f.endsWith('.lean')&&f.startsWith('_AutoProbe_'))){
  const base=f.replace(/^_AutoProbe_/,'').replace(/\.lean$/,'');
  const srcRel='tmp/sheaf/xif/paper/'+base+'.lean';
  if(!existsSync(PAPER+'/'+base+'.lean')) continue;
  const lr=latest(srcRel); if(!lr||!lr.includes('EXIT=0')) continue;
  const txt=readFileSync(PAPER+'/'+base+'.lean','utf8');
  const decls=declsWithNs(txt).slice(0,3);
  if(!decls.length) continue;
  const content='import tmp.sheaf.xif.paper.'+base+'\n\n'+decls.map(d=>'#print axioms '+d).join('\n')+'\n';
  if(readFileSync(PAPER+'/'+f,'utf8')!==content){ writeFileSync(PAPER+'/'+f,content); fixed++; }
}
console.log('probe_contents_fixed='+fixed);
