import { readFileSync, writeFileSync, existsSync, statSync } from 'node:fs';
import { basename } from 'node:path';
const ROOT='D:/lean';
const p=ROOT+'/coord/repo-route-index-data.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const results=readFileSync(ROOT+'/tmp/xif_guarded_results.log','utf8').split('\n');
const lastResult=(rel)=>{ for(let i=results.length-1;i>=0;i--){ if(results[i].includes('FILE='+rel)) return results[i]; } return null; };
const oleanFresh=(rel)=>{ const src=ROOT+'/'+rel; const ole=ROOT+'/.lake/build/lib/lean/'+rel.replace(/\.lean$/,'.olean'); try{ return existsSync(src)&&existsSync(ole)&&statSync(ole).mtimeMs>=statSync(src).mtimeMs; }catch{ return false; } };
const candidates=(rel)=>{ const b=basename(rel); const dirs=['tmp/sheaf/xif/paper','tmp/sheaf/xif','tmp/sheaf','tmp']; return dirs.map(d=>d+'/'+b); };
let remapped=0, changed=0; const cnt={};
for(const r of j.rows){
  let rel=r.file;
  if(!existsSync(ROOT+'/'+rel)){
    for(const c of candidates(rel)){ if(existsSync(ROOT+'/'+c)){ r.original_file=r.file; r.file=c; rel=c; remapped++; break; } }
  }
  const src=ROOT+'/'+rel;
  let st;
  const res=lastResult(rel); const fresh=oleanFresh(rel);
  if(!existsSync(src)) st='STALE_NO_SOURCE';
  else if(res&&res.includes('EXIT=1')) st='EXIT1';
  else if(fresh) st='OLEAN_FRESH';
  else if(res&&res.includes('EXIT=0')) st='EXIT0';
  else st='NO_RESULTS_LINE';
  if(st!==r.citable){ r.citable=st; changed++; }
  cnt[st]=(cnt[st]||0)+1;
}
j.stats.citable=cnt;
writeFileSync(p,JSON.stringify(j,null,2));
console.log('remapped='+remapped+' changed='+changed+' stats='+JSON.stringify(cnt));
