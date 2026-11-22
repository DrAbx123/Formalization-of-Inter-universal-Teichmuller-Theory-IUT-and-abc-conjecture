import { readFileSync, writeFileSync, existsSync, statSync, readdirSync } from 'node:fs';
import { join, basename } from 'node:path';
const ROOT='D:/lean';
const files=['dag/target-chain.json'];
for(const f of readdirSync(ROOT+'/coord')){ if(/^target-chain\..+\.json$/.test(f) && f!=='target-chain.TEMPLATE.json') files.push('coord/'+f); }
const results=readFileSync(ROOT+'/tmp/xif_guarded_results.log','utf8').split('\n');
const lastResult=(rel)=>{ for(let i=results.length-1;i>=0;i--){ if(results[i].includes('FILE='+rel)) return results[i]; } return null; };
const oleanFresh=(rel)=>{ const src=join(ROOT,rel); const ole=join(ROOT,'.lake/build/lib/lean',rel.replace(/\.lean$/,'.olean')); try{ return existsSync(src)&&existsSync(ole)&&statSync(ole).mtimeMs>=statSync(src).mtimeMs; }catch{ return false; } };
let updated=0,total=0;
for(const f of files){
  let j; try{ j=JSON.parse(readFileSync(ROOT+'/'+f,'utf8')); }catch{ continue; }
  for(const n of (j.nodes||[])){
    if(!n.note) continue;
    if(!/pending|await|to verify|PENDING|TODO/i.test(n.note)) continue;
    if(/VERIFIED/i.test(n.note)) continue;
    total++;
    const fs_=(n.files||[]).filter(x=>x.endsWith('.lean'));
    if(fs_.length===0) continue;
    const ok=fs_.every(f=>{ const r=lastResult(f); const fresh=oleanFresh(f); return (fresh || (r&&r.includes('EXIT=0'))) && !(r&&r.includes('EXIT=1')); });
    if(ok){ n.note = 'VERIFIED (results-log/olean evidence; shehdd): '+n.note; updated++; }
  }
  writeFileSync(ROOT+'/'+f, JSON.stringify(j,null,2));
}
console.log('candidate notes='+total+' updated='+updated);
