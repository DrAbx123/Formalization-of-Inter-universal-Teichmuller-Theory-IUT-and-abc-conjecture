import { readdirSync, readFileSync, statSync, writeFileSync, existsSync, mkdirSync } from 'node:fs';
import { join, relative } from 'node:path';
import { createHash } from 'node:crypto';
const ROOT='D:/lean';
const SCAN_DIRS=['LeanFormal','tmp/sheaf/xif/paper','tmp/external/ported','Pi1','PadicLogVolume','TateCurvesTheta','TemperedFundamentalGroups','Oka','EllipticCurves','ContinuousKummerTheory','FormalSchemes','Iut','Genl','Heights','LocalClassFieldTheory','OrbicurveCores','CurvesJacobian','WeilCurves','Belyi']; const OUT=join(ROOT,'dag','generated'); mkdirSync(OUT,{recursive:true});
const skipDirs=new Set(['.lake','.git','node_modules','.dsh']);
const files=[];
function walk(dir){ let es; try{es=readdirSync(dir,{withFileTypes:true});}catch{return;} for(const e of es){ if(e.name.startsWith('.')||skipDirs.has(e.name))continue; const p=join(dir,e.name); if(e.isDirectory())walk(p); else if(e.isFile()&&e.name.endsWith('.lean'))files.push(p); } }
for(const d of SCAN_DIRS) walk(join(ROOT,d));
// A725/A728: include the root vendor umbrella modules explicitly (they are not inside SCAN_DIRS).
for(const _u of ["ContinuousKummerTheory.lean","EllipticCurves.lean","FormalSchemes.lean","Iut.lean","LeanFormal.lean","Oka.lean","PadicLogVolume.lean","Pi1.lean","TateCurvesTheta.lean","TemperedFundamentalGroups.lean"]) { const _p = join(ROOT,_u); if (existsSync(_p)) files.push(_p); }

const rel=(p)=>relative(ROOT,p).replaceAll('\\','/');
const portedRoot=join(ROOT,'tmp','external','ported');
const portedRoots=[]; try{ for(const d of readdirSync(portedRoot,{withFileTypes:true})) if(d.isDirectory()) portedRoots.push(join(portedRoot,d.name)); }catch{}
const roots=[ROOT,...portedRoots];
const rootOf=(p)=>ROOT; // A715: ported module names must be repo-relative (tmp.external.ported...) to match imports
const moduleOf=(p)=>relative(rootOf(p),p).replace(/\.lean$/,'').replaceAll('\\','.');
// module -> instances [{root,path,module}]
const byModRoot=new Map(); // key root+'|'+mod -> path
const allMods=new Map(); // mod -> [{root,path}]
const fileModule=new Map();
for(const p of files){ const r=rootOf(p); const m=moduleOf(p); fileModule.set(p,m); const k=r+'|'+m; byModRoot.set(k,p); if(!allMods.has(m))allMods.set(m,[]); allMods.get(m).push({root:r,path:p}); }
const exitByFile=new Map(); try{ for(const line of readFileSync(join(ROOT,'tmp','xif_guarded_results.log'),'utf8').split(/\r?\n/)){ const m=line.match(/^EXIT=(\d+) FILE=(\S+)/); if(m) exitByFile.set(m[2].replaceAll('\\','/'),Number(m[1])); } }catch{}
const oleanFor=(p)=>{ const r=rootOf(p); const m=moduleOf(p); const cand=[]; if(r===ROOT) cand.push(join(ROOT,'.lake','build','lib','lean',m.replaceAll('.','/')+'.olean')); else cand.push(join(ROOT,'.lake','build','lib','lean',m.replaceAll('.','/')+'.olean'), join(r,'.lake','build','lib','lean',m.replaceAll('.','/')+'.olean')); return cand.find(existsSync)||null; };
const resolveImport=(importerP, imp)=>{ const r=rootOf(importerP); const key=r+'|'+imp; if(byModRoot.has(key)) return {resolved:true, path:byModRoot.get(key), how:'same-root'}; if(byModRoot.has(ROOT+'|'+imp)) return {resolved:true,path:byModRoot.get(ROOT+'|'+imp),how:'repo-root'}; return {resolved:false}; };
const nodes=[]; const edges=[]; const edgeSet=new Set(); const unresolved=new Map(); const ambiguous=[];
for(const p of files){ const r=rel(p); let src=''; try{src=readFileSync(p,'utf8');}catch{} const st=statSync(p); const imports=[...src.matchAll(/^\s*(?:public\s+|private\s+|protected\s+)?import\s+([A-Za-z0-9_.]+)/gm)].map(m=>m[1]); const ole=oleanFor(p);
  nodes.push({ id:'file:'+r, kind:'file', path:r, module:moduleOf(p), root:rootOf(p)===ROOT?'(repo)':rel(rootOf(p)),
    size:st.size, mtime:st.mtime.toISOString(), sha256:createHash('sha256').update(src).digest('hex'),
    olean_present:!!ole, olean_path:ole?rel(ole):null, last_exit:exitByFile.has(r)?exitByFile.get(r):null,
    sorry_tokens:(src.match(/\bsorry\b/g)||[]).length, axiom_decls:(src.match(/^\s*(?:axiom|constant)\s+\S+/gm)||[]).length, import_count:imports.length });
  for(const imp of imports){ const res=resolveImport(p,imp); if(res.resolved){ const rr=rel(res.path); const key='file:'+r+'|file:'+rr; if(!edgeSet.has(key)){edgeSet.add(key); edges.push({from:'file:'+r,to:'file:'+rr,kind:'import',module:imp,resolved_via:res.how});} if(res.ambiguous) ambiguous.push([r,imp,rel(res.path)]); } else unresolved.set(imp,(unresolved.get(imp)||0)+1); }
}
writeFileSync(join(OUT,'nodes-files.json'),JSON.stringify({root:ROOT,file_count:nodes.length,nodes}));
writeFileSync(join(OUT,'edges-imports.json'),JSON.stringify({edge_count:edges.length, edges}));
writeFileSync(join(OUT,'imports-external.json'),JSON.stringify({external_import_names:unresolved.size, top:[...unresolved.entries()].sort((a,b)=>b[1]-a[1]).slice(0,300)}));
const summary={ files:nodes.length, edges:edges.length, external_import_names:unresolved.size, ambiguous_resolutions:ambiguous.length,
  olean_present:nodes.filter(n=>n.olean_present).length, olean_missing:nodes.filter(n=>!n.olean_present).length,
  with_exit0:nodes.filter(n=>n.last_exit===0).length, with_exit_nonzero:nodes.filter(n=>n.last_exit!==null&&n.last_exit!==0).length,
  files_with_sorry_token:nodes.filter(n=>n.sorry_tokens>0).length, files_with_axiom_decl:nodes.filter(n=>n.axiom_decls>0).length };
writeFileSync(join(OUT,'summary.json'),JSON.stringify(summary,null,2));
writeFileSync(join(OUT,'ambiguous-resolutions.json'),JSON.stringify({count:ambiguous.length, sample:ambiguous.slice(0,100)},null,2));
console.log(JSON.stringify(summary,null,2));