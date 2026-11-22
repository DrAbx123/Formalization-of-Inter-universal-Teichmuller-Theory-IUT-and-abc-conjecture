import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { join, dirname } from 'node:path';
const ROOT='D:/lean';
const dag=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const out=ROOT+'/dag/nodes/sheaf'; mkdirSync(out,{recursive:true});
const stmt=new Map(), proof=new Map(), other=new Map();
for(const e of dag.edges){ if(e.kind==='statement'){ (stmt.get(e.from)||stmt.set(e.from,[]).get(e.from)).push(e.to); } }
// rebuild maps cleanly
const S=new Map(), P=new Map(), O=new Map();
for(const e of dag.edges){ if(e.kind==='statement'){ if(!S.has(e.from))S.set(e.from,[]); S.get(e.from).push({to:e.to,evidence:e.evidence||null}); } else if(e.kind==='proof'){ if(!P.has(e.from))P.set(e.from,[]); P.get(e.from).push({to:e.to,evidence:e.evidence||null}); } else { if(!O.has(e.from))O.set(e.from,[]); O.get(e.from).push({to:e.to,kind:e.kind,evidence:e.evidence||null,structural:!!e.derived}); } }
const cand=JSON.parse(readFileSync(ROOT+'/dag/DAG-CANDIDATES.json','utf8')).candidates||[];
const C=new Map(); for(const c of cand){ if(!C.has(c.from))C.set(c.from,[]); C.get(c.from).push(c); }
let n=0;
for(const node of dag.nodes){
  const rec={id:node.id,kind:node.kind,status:node.status,title:node.title||'',source:node.source||null,files:node.files||[],declarations:node.declarations||{},
    statement_dependencies:(S.get(node.id)||[]).map(x=>x.to), proof_dependencies:(P.get(node.id)||[]).map(x=>x.to),
    interface_or_gap:(O.get(node.id)||[]), candidate_connections:(C.get(node.id)||[]).map(x=>x.to), note:node.note||''};
  const safe=node.id.replace(/[^A-Za-z0-9_.-]+/g,'_');
  writeFileSync(join(out,safe+'.json'), JSON.stringify(rec,null,2)); n++; }
writeFileSync(ROOT+'/dag/nodes/sheaf/_index.json', JSON.stringify({generated_at:new Date().toISOString(),nodes:n,policy:'SHEAF: one JSON per node; statement/proof deps separated; candidates not deps'},null,2));
console.log('exported',n,'node json files');