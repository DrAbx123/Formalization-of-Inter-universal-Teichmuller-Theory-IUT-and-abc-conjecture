import { readFileSync, readdirSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const frags=readdirSync(ROOT+'/coord').filter(f=>f.endsWith('.json')&&(f.startsWith('target-chain.iut-skeleton')||f.startsWith('target-chain.iut-pre-'))).sort();
const stats=[];
for(const f of frags){ const j=JSON.parse(readFileSync(ROOT+'/coord/'+f,'utf8')); const nodes=j.nodes||[], edges=j.edges||[];
  const nk={},ns={},ek={},ev={}; for(const n of nodes){nk[n.kind]=(nk[n.kind]||0)+1; ns[n.status]=(ns[n.status]||0)+1;} for(const e of edges){ek[e.kind]=(ek[e.kind]||0)+1; ev[e.evidence||'none']=(ev[e.evidence||'none']||0)+1;}
  const deg=new Map(); for(const n of nodes) deg.set(n.id,0); for(const e of edges){ if(deg.has(e.from)) deg.set(e.from,deg.get(e.from)+1); if(deg.has(e.to)) deg.set(e.to,deg.get(e.to)+1); }
  const iso=[...deg.entries()].filter(([k,v])=>v===0).length;
  const noF=nodes.filter(n=>!(n.files||[]).length).length;
  const noD=nodes.filter(n=>{const d=n.declarations; if(!d) return true; if(Array.isArray(d)) return d.length===0; return Object.values(d).flat().length===0;}).length;
  stats.push({f:f.replace('target-chain.','').replace('.json',''),nodes:nodes.length,edges:edges.length,nk,ns,ek,ev,iso,noF,noD});
}
const fmt=(o)=>Object.entries(o).map(([k,v])=>k+'='+v).join(', ');
const L=[];
for(const s of stats) L.push('| '+s.f+' | '+s.nodes+' | '+s.edges+' | '+fmt(s.nk)+' | '+fmt(s.ns)+' | '+fmt(s.ek)+' | '+fmt(s.ev)+' | '+s.iso+' | '+s.noF+' | '+s.noD+' |');
const T={nodes:0,edges:0,planned:0,observed:0};
for(const s of stats){T.nodes+=s.nodes;T.edges+=s.edges;T.planned+=s.ev.planned||0;T.observed+=s.ev.observed_source||0;}
L.push('| 合计 | '+T.nodes+' | '+T.edges+' | | | | planned='+T.planned+', observed_source='+T.observed+' | | | |');
L.push('');
L.push('要点: (a) iut-skeleton 全部边 evidence=planned（无 observed_source），证据缺口最大; (b) iut-pre-abc/pre-stepxi 节点 declarations 基本为空; (c) iut-pre-mainline 快照为空（正被 owner 迁移/重写，属并发写窗口）; (d) 语义重叠见第 4 节。统计为读取瞬间快照，fragment 正被各单写者并发追加。');
L.push('');
appendFileSync(ROOT+'/coord/SURVEY-shehdd.md', L.join('\n')+'\n');
console.log('chunk2 ok rows='+stats.length);
