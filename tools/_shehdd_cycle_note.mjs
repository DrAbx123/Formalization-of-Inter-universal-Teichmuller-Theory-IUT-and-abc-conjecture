import { readFileSync, writeFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const d=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const ids=new Set(d.nodes.map(n=>n.id));
const edges=d.edges.filter(e=>e.kind!=='statement'&&ids.has(e.from)&&ids.has(e.to));
const adj=new Map(); for(const id of ids) adj.set(id,[]);
for(const e of edges) adj.get(e.from).push(e.to);
let idx=0; const index=new Map(), low=new Map(), onStack=new Set(), stack=[], sccs=[];
const strong=(v)=>{ index.set(v,idx); low.set(v,idx); idx++; stack.push(v); onStack.add(v);
  for(const w of adj.get(v)){ if(!index.has(w)){ strong(w); low.set(v,Math.min(low.get(v),low.get(w))); } else if(onStack.has(w)){ low.set(v,Math.min(low.get(v),index.get(w))); } }
  if(low.get(v)===index.get(v)){ const comp=[]; while(true){ const w=stack.pop(); onStack.delete(w); comp.push(w); if(w===v) break; } sccs.push(comp); } };
for(const id of ids) if(!index.has(id)) strong(id);
const cyc=sccs.filter(c=>c.length>1);
const cycLines=cyc.map(c=>'- SCC size='+c.length+': '+c.join(', ')).join('\n');
const nodeCount=d.nodes.length, edgeCount=d.edges.length;
const p=ROOT+'/coord/DAG-VALIDATION-NOTES.md';
let txt=existsSync(p)?readFileSync(p,'utf8'):'# DAG-VALIDATION-NOTES\n';
const section='## 剩余环（未改边，需 owner 语义决策）\n\n'+(cycLines||'- 无')+'\n\n- 边类别：CONTRACT -> IUTII_LINK_GAP [gap]；IUTII_LINK_GAP -> CONTRACT [interface]。\n- 需 owner 确认错误方向的边；确认前保留现状。\n\n';
if(txt.includes('## 剩余环')){ txt=txt.replace(/## 剩余环[\s\S]*?(?=\n## |$)/, section); } else { txt=txt+'\n'+section; }
txt=txt.replace(/- 最新：[^\n]*/, '- 最新：nodes '+nodeCount+' / edges '+edgeCount+' / problems '+(cyc.length>0?1:0)+'（proof/interface/gap 子图环；SCC 见下）。');
writeFileSync(p,txt);
console.log('cycle section updated; SCCs='+cyc.length);
