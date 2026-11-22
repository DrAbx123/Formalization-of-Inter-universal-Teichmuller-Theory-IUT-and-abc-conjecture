import { readFileSync, writeFileSync, existsSync } from 'node:fs';
import { join } from 'node:path';
const ROOT='D:/lean';
const path=join(ROOT,'coord','target-chain.paper-routes.json');
const j=JSON.parse(readFileSync(path,'utf8'));
let dropped=[]; let fixed=0;
const replFile=(files)=>{ const out=[]; for(const f of files){ if(f.endsWith('S3128Stage1SHEHDDInterfaceActual.lean')){ const cand=f.replace('InterfaceActual','SpecActual'); if(existsSync(join(ROOT,cand))){ out.push(cand); continue; } } out.push(f); } return out; };
for(const n of j.nodes||[]){
  n.files=replFile(n.files||[]);
  const newDecls={};
  for(const [f,names] of Object.entries(n.declarations||{})){
    let nf=f; if(f.endsWith('S3128Stage1SHEHDDInterfaceActual.lean')){ const cand=f.replace('InterfaceActual','SpecActual'); if(existsSync(join(ROOT,cand))) nf=cand; }
    if(!existsSync(join(ROOT,nf))){ dropped.push(n.id+':'+f+' (missing file)'); continue; }
    const src=readFileSync(join(ROOT,nf),'utf8');
    let list=names.map(x=> x==='iutIVProp13i_normalizedDifferent_ge' ? 'iutIVProp13i_normalizedDifferent_eq_of_tame' : x);
    if(nf.endsWith('Comparison.lean')) list=['cor312Conclusion_of_contract'];
    const kept=list.filter(x=>src.includes(x));
    const lost=list.filter(x=>!src.includes(x));
    if(lost.length) dropped.push(n.id+':'+nf+': '+lost.join(','));
    if(kept.length){ newDecls[nf]=kept; fixed++; }
  }
  n.declarations=newDecls;
  if(!n.files.length) delete n.files;
}
writeFileSync(path, JSON.stringify(j,null,2));
console.log(JSON.stringify({nodes:(j.nodes||[]).length, decl_entries:fixed, dropped_count:dropped.length},null,2));
for(const d of dropped.slice(0,40)) console.log('DROPPED: '+d);