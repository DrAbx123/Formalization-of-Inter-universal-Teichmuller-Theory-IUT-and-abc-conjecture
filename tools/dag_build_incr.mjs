import { readdirSync, readFileSync, writeFileSync, existsSync, statSync } from 'node:fs';
import { join, relative, dirname } from 'node:path';
import { createHash } from 'node:crypto';
const ROOT='D:/lean';
const SCAN_DIRS=['LeanFormal','tmp/sheaf/xif/paper','tmp/external/ported','Pi1','PadicLogVolume','TateCurvesTheta','TemperedFundamentalGroups','Oka','EllipticCurves','ContinuousKummerTheory','FormalSchemes','Iut','Genl','Heights','LocalClassFieldTheory','OrbicurveCores','CurvesJacobian','WeilCurves','Belyi']; const GEN=join(ROOT,'dag','generated');
const t0=Date.now();
const skip=new Set(['.lake','.git','node_modules','.dsh']); const files=[];
function walk(d){ let es; try{es=readdirSync(d,{withFileTypes:true});}catch{return;} for(const e of es){ if(e.name.startsWith('.')||skip.has(e.name))continue; const p=join(d,e.name); if(e.isDirectory())walk(p); else if(e.isFile()&&e.name.endsWith('.lean'))files.push(p); } }
for(const d of SCAN_DIRS) walk(join(ROOT,d));
// A725/A728: include the root vendor umbrella modules explicitly (they are not inside SCAN_DIRS).
for(const _u of ["ContinuousKummerTheory.lean","EllipticCurves.lean","FormalSchemes.lean","Iut.lean","LeanFormal.lean","Oka.lean","PadicLogVolume.lean","Pi1.lean","TateCurvesTheta.lean","TemperedFundamentalGroups.lean"]) { const _p = join(ROOT,_u); if (existsSync(_p)) files.push(_p); }

const rel=(p)=>relative(ROOT,p).replaceAll('\\','/');
let prevNodes=[], prevEdges=[];
try{ prevNodes=JSON.parse(readFileSync(join(GEN,'nodes-files.json'),'utf8')).nodes; }catch{}
try{ prevEdges=JSON.parse(readFileSync(join(GEN,'edges-imports.json'),'utf8')).edges; }catch{}
const prevByPath=new Map(); for(const n of prevNodes) prevByPath.set(n.path,n);
const prevImports=new Map(); for(const e of prevEdges){ const f=e.from.replace(/^file:/,''); const t=e.to.replace(/^file:/,''); if(!prevImports.has(f))prevImports.set(f,[]); prevImports.get(f).push(t); }
const nodes=[]; const edges=[]; let changed=0; const newPaths=new Set();
for(const p of files){ const r=rel(p); newPaths.add(r); const st=statSync(p); const old=prevByPath.get(r);
  if(old && old.size===st.size && old.mtime===st.mtime.toISOString()){ nodes.push(old); const imps=prevImports.get(r)||[]; for(const t of imps) edges.push({from:'file:'+r,to:'file:'+t,kind:'import'}); continue; }
  changed++; let src=''; try{src=readFileSync(p,'utf8');}catch{}
  const imports=[...src.matchAll(/^\s*(?:public\s+|private\s+|protected\s+)?import\s+([A-Za-z0-9_.]+)/gm)].map(m=>m[1]);
  const oleanPath=join(ROOT,'.lake','build','lib','lean',r.replace(/\.lean$/,'')+'.olean');
  const oleanExists=existsSync(oleanPath);
  nodes.push({ id:'file:'+r, kind:'file', path:r, module:r.replace(/\.lean$/,'').replaceAll('/','.'), size:st.size, mtime:st.mtime.toISOString(),
    sha256:createHash('sha256').update(src).digest('hex'), olean_present:oleanExists, olean_path:oleanExists?relative(ROOT,oleanPath).replaceAll('\\','/'):null,
    last_exit:null, sorry_tokens:(src.match(/\bsorry\b/g)||[]).length, axiom_decls:(src.match(/^\s*(?:axiom|constant)\s+\S+/gm)||[]).length });
  // store raw imports names on node temporarily for resolution
  nodes[nodes.length-1]._imps=imports;
}
// module -> path map (prefer repo-root paths); first pass old, then new
const mod2path=new Map();
for(const n of prevNodes){ const m=n.module; if(m && n.path===m.replaceAll('.','/')+'.lean') mod2path.set(m,n.path); }
for(const n of nodes){ if(n._imps) mod2path.set(n.module,n.path); }
for(const n of nodes){ if(!n._imps) continue; for(const imp of n._imps){ const target=mod2path.get(imp); if(target) edges.push({from:'file:'+n.path,to:'file:'+target,kind:'import'}); } delete n._imps; }
const deleted=prevNodes.filter(n=>!newPaths.has(n.path)).length;
writeFileSync(join(GEN,'nodes-files.json'), JSON.stringify({root:ROOT,file_count:nodes.length,nodes}));
writeFileSync(join(GEN,'edges-imports.json'), JSON.stringify({edge_count:edges.length,edges}));
const summary={files:nodes.length,edges:edges.length,changed,deleted,oleans:nodes.filter(n=>n.olean_present).length,ms:Date.now()-t0};
writeFileSync(join(GEN,'summary.json'), JSON.stringify(summary,null,2));
console.log(JSON.stringify(summary));