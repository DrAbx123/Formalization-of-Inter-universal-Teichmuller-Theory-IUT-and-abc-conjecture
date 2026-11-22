import { readFileSync, writeFileSync, existsSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const PAPER=ROOT+'/tmp/sheaf/xif/paper';
const lines=readFileSync(ROOT+'/tmp/xif_guarded_results.log','utf8').split('\n');
const latest=(rel)=>{ for(let i=lines.length-1;i>=0;i--){ if(lines[i].includes('FILE='+rel)) return lines[i]; } return null; };
const probeState=new Map();
for(const l of lines){ const m=l.match(/^EXIT=(\d+) FILE=(tmp\/sheaf\/xif\/paper\/[^\s]*[Pp]robe[^\s]*\.lean)/); if(m) probeState.set(m[2],m[1]); }
const existing=readdirSync(PAPER);
const missing=[...probeState.keys()].filter(p=>!existsSync(ROOT+'/'+p));
const plain=existing.filter(f=>f.endsWith('.lean')&&!f.startsWith('_')).map(f=>f.replace(/\.lean$/,''));
const rows=[];
for(const p of missing){
  const stem=p.split('/').pop().replace(/\.lean$/,'');
  const clean=stem.replace(/^_/,'').replace(/Probe/g,'').replace(/\d+$/,'').replace(/_+$/,'');
  const cands=plain.filter(b=>clean.length>2 && (b.startsWith(clean)||clean.startsWith(b)||b.includes(clean))).sort((a,b)=>b.length-a.length);
  let src=null, srcResult=null;
  for(const b of cands){ const rel='tmp/sheaf/xif/paper/'+b+'.lean'; const lr=latest(rel); if(!src){ src=b; srcResult=lr; } if(lr&&lr.includes('EXIT=0')){ src=b; srcResult=lr; break; } }
  rows.push({probe:p, stem, lastExit:probeState.get(p), source:src, sourceLatest:srcResult?srcResult.slice(0,110):null});
}
writeFileSync(ROOT+'/tmp/_probe_audit_rows.json', JSON.stringify(rows,null,1));
console.log('rows='+rows.length);
for(const r of rows) console.log(r.lastExit+' | '+r.stem+' | src='+r.source+' | '+(r.sourceLatest?r.sourceLatest.slice(0,60):'no-result'));
