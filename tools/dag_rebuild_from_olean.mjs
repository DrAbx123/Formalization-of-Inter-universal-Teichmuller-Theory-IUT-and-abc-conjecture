// Canonical DAG rebuild: ground truth = .olean files; nodes = compiled modules, edges = source imports.
// Writes dag/declaration-dag.json (schema-compatible) + dag/OLEAN-DAG.json (same data) + md.
import { readFileSync, writeFileSync, existsSync, readdirSync, statSync } from 'node:fs';
import { join, relative } from 'node:path';
const ROOT='D:/lean';
const BUILD=join(ROOT,'.lake','build','lib','lean');
const SHADOW=join(ROOT,'.lean-shadow','project');
function walk(dir,out){ let ents=[]; try{ ents=readdirSync(dir,{withFileTypes:true}); }catch{ return out; } for(const e of ents){ const p=join(dir,e.name); if(e.isDirectory()) walk(p,out); else if(e.name.endsWith('.olean')) out.push(p); } return out; }
const uniq=new Map();
const add=(list,base)=>{ for(const o of list){ const rel=relative(base,o).replace(/\\/g,'/').replace(/\.olean$/,''); if(!uniq.has(rel)) uniq.set(rel,{module:rel, olean:o}); } };
add(walk(BUILD,[]),BUILD); add(walk(SHADOW,[]),SHADOW);
const stripComments=(s)=>{ let out=''; let i=0; const n=s.length; while(i<n){ if(s.startsWith('/-',i)){ let depth=1; i+=2; while(i<n && depth>0){ if(s.startsWith('/-',i)){ depth++; i+=2; } else if(s.startsWith('-/',i)){ depth--; i+=2; } else i++; } continue; } if(s.startsWith('--',i)){ const j=s.indexOf('\n',i); i=(j<0?n:j); continue; } if(s[i]==='"'){ i++; while(i<n){ if(s[i]==='\\'){ i+=2; continue; } if(s[i]==='"'){ i++; break; } i++; } out+=' '; continue; } out+=s[i]; i++; } return out; };
const sorryRe=/\bsorry\b/g;
const declRe=/^\s*(?:private\s+|protected\s+|noncomputable\s+|@\[[^\]]*\]\s*)*(theorem|lemma|def|abbrev|structure|class|inductive|instance)\s+([A-Za-z0-9_'.]+)/gm;
const importRe=/^\s*import\s+([A-Za-z0-9_.']+)/gm;
const nodes=[], edges=[], moduleToId=new Map(), srcOf=new Map();
let blockedFiles=new Map(); try{ const b=JSON.parse(readFileSync(join(ROOT,'coord','DAG-BLOCKED.json'),'utf8')).blocked||[]; for(const e of b){ const id=String(e.id||''); const n8=id.match(/^sorries:n8-closure:(.+)$/); if(n8) blockedFiles.set('tmp/sheaf/n8/closure/'+n8[1]+'.lean', e.reason||'blocked');
    else { const ol=id.match(/^olean:(.+)$/); const xf=id.match(/^xif-sorry:(.+)$/);
      if(ol) blockedFiles.set(ol[1]+'.lean', e.reason||'blocked');
      else if(xf) blockedFiles.set('tmp/sheaf/xif/paper/'+xf[1]+'.lean', e.reason||'blocked');
      else if(e.file) blockedFiles.set(e.file, e.reason||'blocked'); } } }catch{}
let missingSrc=0, totalDecls=0, totalSorry=0, sorryModules=0;
for(const [mod,info] of uniq){
  const srcPath=join(ROOT, mod+'.lean');
  if(!existsSync(srcPath)){ missingSrc++; continue; }
  let src=''; try{ src=readFileSync(srcPath,'utf8'); }catch{ missingSrc++; continue; }
  const decls=[]; let m; declRe.lastIndex=0; while((m=declRe.exec(src))) decls.push({name:m[2],kind:m[1]}); totalDecls+=decls.length;
  const code=stripComments(src); const sm=code.match(sorryRe); const sorryCount=sm?sm.length:0; totalSorry+=sorryCount;
  const id='olean:'+mod;
  const hasTheorem=decls.some(d=>d.kind==='theorem'||d.kind==='lemma');
  if(sorryCount>0) sorryModules++;
  const relFile=relative(ROOT,srcPath).replace(/\\/g,'/'); const blockedReason=blockedFiles.get(relFile);
  nodes.push({id, kind: hasTheorem?'theorem':'def', status: blockedReason?'GAP':(sorryCount>0?'CONDITIONAL':'PROVED'), sorry_count:sorryCount, blocked: blockedReason||undefined, module:mod, files:[relative(ROOT,srcPath).replace(/\\/g,'/')], olean:relative(ROOT,info.olean).replace(/\\/g,'/'), declarations:{[relative(ROOT,srcPath).replace(/\\/g,'/')]: decls.map(d=>d.name)}, decl_count:decls.length, evidence:'olean', title:mod});
  moduleToId.set(mod.split('/').join('.'), id); srcOf.set(id,src);
}
let resolved=0, unresolved=0;
for(const n of nodes){ const src=srcOf.get(n.id); let m; const imps=[]; importRe.lastIndex=0; while((m=importRe.exec(src))) imps.push(m[1]);
  for(const im of imps){ const t=moduleToId.get(im); if(t){ edges.push({from:n.id,to:t,kind:'statement',evidence:'observed_source'}); resolved++; } else unresolved++; } }
const meta={generated_at:new Date().toISOString(), ground_truth:'olean files', nodes:nodes.length, edges:edges.length, resolved_imports:resolved, unresolved_imports:unresolved, missing_source:missingSrc, total_decls:totalDecls};
writeFileSync(join(ROOT,'dag','OLEAN-DAG.json'), JSON.stringify({meta,nodes,edges},null,2));
writeFileSync(join(ROOT,'dag','declaration-dag.json'), JSON.stringify({generated_by:'tools/dag_rebuild_from_olean.mjs',meta,node_count:nodes.length,edge_count:edges.length,conflicts:[],nodes,edges},null,2));
const md=['# OLEAN DAG (canonical; ground truth = compiled .olean files)','','generated: '+meta.generated_at,'','| metric | value |','|---|---|','| nodes (compiled modules) | '+nodes.length+' |','| edges (imports) | '+edges.length+' |','| resolved imports | '+resolved+' |','| unresolved imports (Mathlib/external) | '+unresolved+' |','| olean without source | '+missingSrc+' |','| declarations | '+totalDecls+' |','| modules containing sorry | '+sorryModules+' |','| sorry occurrences (code, comments stripped) | '+totalSorry+' |'];
writeFileSync(join(ROOT,'dag','OLEAN-DAG.md'), md.join('\n'));
console.log(JSON.stringify(meta,null,2));