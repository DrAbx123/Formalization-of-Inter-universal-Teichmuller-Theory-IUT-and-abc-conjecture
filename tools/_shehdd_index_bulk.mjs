import { readFileSync, writeFileSync, existsSync, statSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/repo-route-index-data.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const results=readFileSync(ROOT+'/tmp/xif_guarded_results.log','utf8').split('\n');
const lastResult=(rel)=>{ for(let i=results.length-1;i>=0;i--){ if(results[i].includes('FILE='+rel)) return results[i]; } return null; };
const oleanFresh=(rel)=>{ const src=join0(ROOT,rel); const ole=join0(ROOT,'.lake/build/lib/lean',rel.replace(/\.lean$/,'.olean')); try{ return existsSync(src)&&existsSync(ole)&&statSync(ole).mtimeMs>=statSync(src).mtimeMs; }catch{ return false; } };
function join0(a,b){ return a.replace(/\/$/,'')+'/'+b; }
let upd={};
for(const r of j.rows){
  if(!['NO_RESULTS_LINE','OLEAN_MISSING'].includes(r.citable)) continue;
  const rel=r.file;
  const fresh=oleanFresh(rel);
  const res=lastResult(rel);
  const exit0=res&&res.includes('EXIT=0');
  if(fresh||exit0){ r.citable = exit0?'EXIT0':(fresh?'OLEAN_FRESH':r.citable); r.index_note='shehdd A460 evidence update: '+(exit0?'results-log EXIT0':'olean fresh')+(fresh?' + olean fresh':''); upd[r.citable]=(upd[r.citable]||0)+1; }
}
if(j.stats&&j.stats.citable){ for(const k of Object.keys(upd)){ /* recompute basic counts */ } 
  const cnt={}; for(const r of j.rows){ cnt[r.citable]=(cnt[r.citable]||0)+1; } j.stats.citable=Object.assign(j.stats.citable,cnt); }
writeFileSync(p, JSON.stringify(j,null,2));
console.log('updated='+JSON.stringify(upd));
