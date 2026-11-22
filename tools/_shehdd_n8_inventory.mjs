import { readdirSync, statSync, readFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const lines=readFileSync(ROOT+'/tmp/xif_guarded_results.log','utf8').split('\n');
const latest=(rel)=>{ for(let i=lines.length-1;i>=0;i--){ if(lines[i].includes('FILE='+rel)) return lines[i]; } return null; };
const dirs=[...new Set(readdirSync(ROOT+'/tmp').filter(d=>d.startsWith('n8')).map(d=>'tmp/'+d).concat(
  existsSync(ROOT+'/tmp/sheaf')?readdirSync(ROOT+'/tmp/sheaf').filter(d=>d.startsWith('n8')).map(d=>'tmp/sheaf/'+d):[]))];
const rows=[];
for(const d of dirs){
  let files=[]; const walk=(rel)=>{ let ents; try{ ents=readdirSync(ROOT+'/'+rel,{withFileTypes:true}); }catch{ return; } for(const e of ents){ const p=rel+'/'+e.name; if(e.isDirectory()){ if(/node_modules|__pycache__|\.lake/.test(p)) continue; walk(p); } else if(e.name.endsWith('.lean')) files.push(p); } };
  walk(d);
  let ok=0, fail=0, none=0, recent=0; let bytes=0;
  for(const f of files){ bytes+=statSync(ROOT+'/'+f).size; const lr=latest(f); if(!lr) none++; else if(lr.includes('EXIT=0')) ok++; else fail++; const mt=statSync(ROOT+'/'+f).mtimeMs; if(Date.now()-mt<3600*1000) recent++; }
  rows.push({dir:d,lean:files.length,MB:(bytes/1048576).toFixed(1),ok,fail,none,recent});
}
console.log(JSON.stringify(rows,null,1));
// legacy fragment stats
for(const f of ['coord/target-chain.legacy-dag.json']){ if(existsSync(ROOT+'/'+f)){ try{ const j=JSON.parse(readFileSync(ROOT+'/'+f,'utf8')); const cnt={}; for(const n of j.nodes) cnt[n.status]=(cnt[n.status]||0)+1; console.log(f+' nodes='+j.nodes.length+' edges='+j.edges.length+' status='+JSON.stringify(cnt)); }catch(e){ console.log(f+' parse error'); } } }
