import { readFileSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const idx=JSON.parse(readFileSync(ROOT+'/dag/generated/declarations-index.json','utf8')).declarations;
for(const t of ['ChebyshevBound','PrimeCountingBound','chebyshevBound','primeCountingBound','ExplicitEstimate','LocalEstimate','PrimeSelection','HeightBound']){
  const hits=idx.filter(d=>d.name.includes(t));
  console.log('##',t,hits.length);
  for(const h of hits.slice(0,12)) console.log(' ',h.kind,h.name,'@',h.file);
}
console.log('--- external lana repo stats ---');
function walk(d,out){ let e=[]; try{e=readdirSync(d,{withFileTypes:true})}catch{ return out; } for(const x of e){ const p=d+'/'+x.name; if(x.isDirectory()) walk(p,out); else out.push(p); } return out; }
const base=ROOT+'/tmp/dsh-oct6-openai-math-survey-20261016/repos/lana/iut/iut-main';
const all=walk(base,[]); console.log('files',all.length);
const lean=all.filter(f=>f.endsWith('.lean')); console.log('lean files',lean.length);
const byDir={}; for(const f of lean){ const rel=f.slice(base.length+1); const d=rel.split('/').slice(0,2).join('/'); byDir[d]=(byDir[d]||0)+1; } console.log(JSON.stringify(Object.entries(byDir).sort((a,b)=>b[1]-a[1]).slice(0,20)));