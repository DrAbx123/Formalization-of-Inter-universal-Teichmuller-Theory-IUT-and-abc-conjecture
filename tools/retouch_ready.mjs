
import { readFileSync, existsSync, utimesSync, statSync } from 'node:fs';
const ROOT='D:/lean';
const statePath=ROOT+'/dag/watchdog/state.json';
const portedPrefix=ROOT+'/tmp/external/ported/';
const importRe=/^\s*import\s+([A-Za-z0-9_.']+)/gm;
function oleanCandidates(file){
  const rel=file.replace(/\.lean$/,'');
  if(file.startsWith('tmp/external/ported/')){
    const rest=file.slice('tmp/external/ported/'.length);
    const pkg=rest.split('/')[0];
    const pkgRoot='tmp/external/ported/'+pkg+'/';
    const modRel=file.slice(pkgRoot.length).replace(/\.lean$/,'');
    return [ROOT+'/.lake/build/lib/lean/'+modRel+'.olean'];
  }
  return [ROOT+'/.lake/build/lib/lean/'+rel+'.olean'];
}
function depsOk(file){
  let s=''; try{ s=readFileSync(ROOT+'/'+file,'utf8'); }catch{ return false; }
  let mm; importRe.lastIndex=0;
  while((mm=importRe.exec(s))){
    const im=mm[1];
    if(/^(Mathlib|Lean|Std|Batteries|Qq|Aesop|ProofWidgets|ImportGraph|Plausible|LeanSearchClient)/.test(im)) continue;
    const modRel=im.replaceAll('.','/');
    const cands=[ROOT+'/.lake/build/lib/lean/'+modRel+'.olean'];
    // also ported mapping: if module starts with tmp.external.ported.<pkg>.
    if(im.startsWith('tmp.external.ported.')){
      const parts=im.split('.');
      const pkg=parts[3];
      const rest=parts.slice(4).join('.');
      cands.push(ROOT+'/tmp/external/ported/'+pkg+'/.lake/build/lib/lean/'+rest.replaceAll('.','/')+'.olean');
    }
    if(!cands.some(existsSync)) return false;
  }
  return true;
}
let state={};
try{ state=JSON.parse(readFileSync(statePath,'utf8')); }catch{ console.log('no state'); process.exit(0); }
let touched=0;
for(const [file,e] of Object.entries(state)){
  if(!e || e.failed_exit===undefined) continue;
  const abs=ROOT+'/'+file;
  if(!existsSync(abs)) continue;
  if(!depsOk(file)) continue;
  // touch to now so mtime > olean
  const now=new Date();
  try{ utimesSync(abs, now, now); touched++; }catch{}
}
console.log('touched', touched);
