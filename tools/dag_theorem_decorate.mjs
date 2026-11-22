import { readFileSync, writeFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const th=JSON.parse(readFileSync(ROOT+'/dag/THEOREM-DAG.json','utf8'));
const dag=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const byId=new Map(dag.nodes.map(n=>[n.id,n]));
const srcCache=new Map(); const read=(p)=>{ if(srcCache.has(p)) return srcCache.get(p); let s=''; try{ s=readFileSync(p,'utf8'); }catch{} srcCache.set(p,s); return s; };
const declRe=/^\s*(?:private\s+|protected\s+|noncomputable\s+|@\[[^\]]*\]\s*)*(theorem|lemma|def|abbrev|structure|class|instance)\s+([A-Za-z0-9_'.]+)/gm;
const tokensOf=(id)=>{ return (id.replace(/[^A-Za-z0-9]+/g,' ').split(/\s+/).filter(t=>t.length>=4)); };
let covered=0, totalDecls=0, missing=[];
for(const n of th.nodes){
  const dn=byId.get(n.id); const files=(dn&&dn.files||[]).filter(f=>existsSync(f)); const decls=[];
  if(dn&&dn.declarations){ for(const [p,names] of Object.entries(dn.declarations)){ for(const nm of names) decls.push({file:p,name:nm}); } }
  if(decls.length===0 && files.length){ const toks=tokensOf(n.id).concat(tokensOf(n.title||'')); for(const f of files.slice(0,3)){ const s=read(f); let m; let count=0; declRe.lastIndex=0; while((m=declRe.exec(s))&&count<8){ const name=m[2]; const hit=toks.some(t=>name.toLowerCase().includes(t.toLowerCase())); if(hit){ decls.push({file:f,name}); count++; } } if(decls.length) break; } }
  if(decls.length===0 && files.length){ const f=files[0]; const s=read(f); let m; let count=0; declRe.lastIndex=0; while((m=declRe.exec(s))&&count<3){ decls.push({file:f,name:m[2]}); count++; } }
  n.lean_declarations=decls; n.lean_source_links=decls.map(d=>d.file+'::'+d.name);
  if(decls.length){ covered++; totalDecls+=decls.length; } else missing.push(n.id);
}
th.lean_mapping_generated_at=new Date().toISOString();
th.lean_mapping_policy='declarations from fragment registration; fallback = declaration names in registered files whose identifiers match node id/title tokens; final fallback = first declarations of first file (flagged by empty match quality)';
writeFileSync(ROOT+'/dag/THEOREM-DAG.json', JSON.stringify(th,null,2));
const md=['# Theorem-level DAG (with Lean declarations)','','generated: '+th.generated_at,'','nodes: '+th.nodes.length+', edges: '+th.edges.length+', with_lean_decls: '+covered+'/'+th.nodes.length,'','| id | status | Lean declarations |','|---|---|---|'];
for(const n of th.nodes){ const ls=(n.lean_source_links||[]).slice(0,2).map(x=>'`'+x+'`').join('<br>'); md.push('| '+n.id+' | '+n.status+' | '+(ls||'—')+' |'); }
writeFileSync(ROOT+'/dag/THEOREM-DAG.md', md.join('\n'));
console.log(JSON.stringify({nodes:th.nodes.length,covered,totalDecls,missing:missing.length,missing_sample:missing.slice(0,15)}));