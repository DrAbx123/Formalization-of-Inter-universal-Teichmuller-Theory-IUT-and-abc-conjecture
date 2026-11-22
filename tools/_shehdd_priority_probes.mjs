import { readFileSync, writeFileSync, existsSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const PAPER=ROOT+'/tmp/sheaf/xif/paper';
const lines=readFileSync(ROOT+'/tmp/xif_guarded_results.log','utf8').split('\n');
const latest=(rel)=>{ for(let i=lines.length-1;i>=0;i--){ if(lines[i].includes('FILE='+rel)) return lines[i]; } return null; };
const stripComments=(txt)=>{ const out=[]; let depth=0; for(const raw of txt.split('\n')){ let res=''; let i=0; while(i<raw.length){ if(depth===0){ if(raw.startsWith('/-',i)){ depth=1; i+=2; continue; } if(raw.startsWith('--',i)) break; res+=raw[i]; i++; } else { if(raw.startsWith('/-',i)){ depth++; i+=2; continue; } if(raw.startsWith('-/',i)){ depth--; i+=2; continue; } i++; } } out.push(res); } return out.join('\n'); };
const decls=(txtRaw)=>{ const txt=stripComments(txtRaw); const out=[]; const stack=[]; const FQN=()=>stack.filter(s=>s.kind==='ns').map(s=>s.name).join('.');
  for(const raw of txt.split('\n')){ const line=raw.trim(); if(!line) continue;
    const mNs=line.match(/^namespace\s+([A-Za-z0-9_.']+)\s*$/); if(mNs){ stack.push({kind:'ns',name:mNs[1]}); continue; }
    if(/^(?:noncomputable\s+)?section\b/.test(line)){ stack.push({kind:'sec'}); continue; }
    if(/^end(\s+[A-Za-z0-9_.']+)?\s*$/.test(line)){ if(stack.length) stack.pop(); continue; }
    const m=line.match(/^(?:theorem|lemma|def|abbrev|structure|inductive)\s+([A-Za-z0-9_']+(?:\.[A-Za-z0-9_']+)*)(?=\s|$)/);
    if(m){ const ns=FQN(); out.push(ns? ns+'.'+m[1] : m[1]); }
  } return out; };
const prio=readFileSync(ROOT+'/dag/watchdog/priority-files.txt','utf8').split('\n').map(x=>x.trim()).filter(Boolean);
let written=0; const added=[];
for(const rel of prio){
  const base=rel.split('/').pop().replace(/\.lean$/,'');
  const src=ROOT+'/'+rel; if(!existsSync(src)) continue;
  const lr=latest(rel); if(!lr||!lr.includes('EXIT=0')) continue;
  const hasProbe=readdirSync(PAPER).some(f=>f.includes(base)&&/Probe|probe/.test(f)) || existsSync(PAPER+'/_AutoProbe_'+base+'.lean');
  if(hasProbe) continue;
  const ds=decls(readFileSync(src,'utf8')).slice(0,3);
  if(!ds.length) continue;
  writeFileSync(PAPER+'/_AutoProbe_'+base+'.lean','import tmp.sheaf.xif.paper.'+base+'\n\n'+ds.map(d=>'#print axioms '+d).join('\n')+'\n');
  added.push('tmp/sheaf/xif/paper/_AutoProbe_'+base+'.lean'); written++;
}
const extra=ROOT+'/dag/watchdog/extra-targets.txt';
const cur=readFileSync(extra,'utf8').split('\n').map(x=>x.trim()).filter(Boolean);
const set=new Set(cur); for(const a of added) set.add(a);
const out=[...set].sort();
writeFileSync(extra,out.join('\n')+'\n');
console.log('priority_probes_written='+written+' targets='+out.length);
