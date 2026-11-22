import { readFileSync, writeFileSync, existsSync, statSync } from 'node:fs';
import { join, basename } from 'node:path';
const ROOT='D:/lean';
const files=['dag/target-chain.json', ...['coord'].flatMap(()=>[])];
import { readdirSync } from 'node:fs';
for(const f of readdirSync(join(ROOT,'coord'))){ if(/^target-chain\..+\.json$/.test(f) && f!=='target-chain.TEMPLATE.json') files.push('coord/'+f); }
const results=(()=>{ try{ return readFileSync(join(ROOT,'tmp/xif_guarded_results.log'),'utf8').split('\n'); }catch{ return []; } })();
const lastResult=(rel)=>{ const base=basename(rel).replace(/\.lean$/,''); for(let i=results.length-1;i>=0;i--){ if(results[i].includes('FILE='+rel)) return results[i]; } return null; };
const oleanFresh=(rel)=>{ const src=join(ROOT,rel); const ole=join(ROOT,'.lake/build/lib/lean',rel.replace(/\.lean$/,'.olean')); try{ return existsSync(src)&&existsSync(ole)&&statSync(ole).mtimeMs>=statSync(src).mtimeMs; }catch{ return false; } };
let updated=0, total=0;
for(const f of files){
  let j; try{ j=JSON.parse(readFileSync(join(ROOT,f),'utf8')); }catch{ continue; }
  for(const n of (j.nodes||[])){
    if(!n.note || !/PENDING/i.test(n.note)) continue;
    total++;
    const fs_=n.files||[];
    if(fs_.length===0) continue;
    const allFresh=fs_.every(oleanFresh);
    const res=fs_.map(lastResult);
    const allExit0=res.every(r=>r&&r.includes('EXIT=0'));
    if(allFresh && allExit0){ n.note = n.note.replace(/PENDING-VERIFY[^.\n]*/i,'VERIFIED (results-log EXIT0 + olean fresh; verified by shehdd)'); updated++; }
  }
  writeFileSync(join(ROOT,f), JSON.stringify(j,null,2));
}
console.log('PENDING notes total='+total+' verified/updated='+updated);
