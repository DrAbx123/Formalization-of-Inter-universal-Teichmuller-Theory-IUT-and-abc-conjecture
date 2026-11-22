import { readFileSync, writeFileSync, existsSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const PAPER=ROOT+'/tmp/sheaf/xif/paper';
const lines=readFileSync(ROOT+'/tmp/xif_guarded_results.log','utf8').split('\n');
const latest=(rel)=>{ for(let i=lines.length-1;i>=0;i--){ if(lines[i].includes('FILE='+rel)) return lines[i]; } return null; };
const probeState=new Map();
for(const l of lines){ const m=l.match(/^EXIT=(\d+) FILE=(tmp\/sheaf\/xif\/paper\/[^\s]*[Pp]robe[^\s]*\.lean)/); if(m) probeState.set(m[2],m[1]); }
const existing=readdirSync(PAPER);
const missing=[...probeState.keys()].filter(p=>!existsSync(ROOT+'/'+p));
// find source base for each missing probe
const plain=existing.filter(f=>f.endsWith('.lean')&&!f.startsWith('_')).map(f=>f.replace(/\.lean$/,''));
const declsWithNs=(txt)=>{ const out=[]; const stack=[]; for(const raw of txt.split('\n')){ const line=raw.trim(); const mNs=line.match(/^namespace\s+([A-Za-z0-9_.']+)\s*$/); if(mNs){ stack.push(mNs[1]); continue; } if(/^end(\s|$)/.test(line)){ if(stack.length) stack.pop(); continue; } const m=line.match(/^(?:theorem|lemma|def|abbrev)\s+([A-Za-z0-9_'.]+)/); if(m){ const full=stack.length? stack.join('.')+'.'+m[1] : m[1]; out.push(full); } } return out; };
let restored=0; const names=[];
for(const p of missing){
  const stem=p.split('/').pop().replace(/\.lean$/,'');
  // candidate source bases whose name is a prefix of the probe stem
  const cands=plain.filter(b=>stem.includes(b)).sort((a,b)=>b.length-a.length);
  let done=false;
  for(const b of cands){
    const srcRel='tmp/sheaf/xif/paper/'+b+'.lean';
    const lr=latest(srcRel);
    if(!lr||!lr.includes('EXIT=0')) continue;
    const txt=readFileSync(PAPER+'/'+b+'.lean','utf8');
    const decls=declsWithNs(txt).filter(d=>!d.includes('sorryAx')).slice(0,3);
    if(!decls.length) continue;
    writeFileSync(ROOT+'/'+p,'import tmp.sheaf.xif.paper.'+b+'\n\n'+decls.map(d=>'#print axioms '+d).join('\n')+'\n');
    restored++; names.push(stem+' <- '+b); done=true; break;
  }
  if(!done) names.push(stem+' <- (no green source, left deleted)');
}
console.log('restored='+restored+'/'+missing.length);
console.log(names.slice(0,40).join('\n'));
