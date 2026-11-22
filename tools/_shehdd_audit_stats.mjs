import { readFileSync, readdirSync, writeFileSync } from 'node:fs';
const ROOT='D:/lean';
const files=readdirSync(ROOT+'/coord').filter(f=>/^target-chain\.iut-(skeleton|pre-.*)\.json$/.test(f)).sort();
const data={};
for(const f of files){
  const j=JSON.parse(readFileSync(ROOT+'/coord/'+f,'utf8'));
  const nodes=j.nodes||[], edges=j.edges||[];
  const nk={},ns={},ek={},ev={};
  for(const n of nodes){ nk[n.kind]=(nk[n.kind]||0)+1; ns[n.status]=(ns[n.status]||0)+1; }
  for(const e of edges){ ek[e.kind]=(ek[e.kind]||0)+1; ev[e.evidence||'none']=(ev[e.evidence||'none']||0)+1; }
  const deg=new Map(); for(const n of nodes) deg.set(n.id,{in:0,out:0});
  for(const e of edges){ if(deg.has(e.from)) deg.get(e.from).out++; if(deg.has(e.to)) deg.get(e.to).in++; }
  const isolated=[...deg.entries()].filter(([k,v])=>v.in===0&&v.out===0).map(([k])=>k);
  const noFiles=nodes.filter(n=>!(n.files||[]).length).map(n=>n.id);
  const noDecls=nodes.filter(n=>{const d=n.declarations; if(!d) return true; if(Array.isArray(d)) return d.length===0; return Object.values(d).flat().length===0;}).map(n=>n.id);
  data[f]={nodes:nodes.length,edges:edges.length,nodeKinds:nk,statuses:ns,edgeKinds:ek,evidence:ev,isolated,noFiles,noDecls};
}
writeFileSync(ROOT+'/tmp/_iut_prereq_stats.json',JSON.stringify(data,null,2));
console.log(JSON.stringify(data,null,1).slice(0,6000));
