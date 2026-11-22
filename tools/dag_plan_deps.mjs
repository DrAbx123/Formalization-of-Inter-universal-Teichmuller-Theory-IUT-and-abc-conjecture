import { readFileSync, writeFileSync, existsSync } from 'node:fs';
import { join } from 'node:path';
const ROOT='D:/lean'; const OUT=join(ROOT,'dag','watchdog');
const plan=JSON.parse(readFileSync(join(OUT,'plan.json'),'utf8'));
const dirtySet=new Set(plan.dirty);
const nodes=JSON.parse(readFileSync(join(ROOT,'dag','generated','nodes-files.json'),'utf8')).nodes;
const imports=new Map(); for(const n of nodes) imports.set(n.path,[]);
const edges=JSON.parse(readFileSync(join(ROOT,'dag','generated','edges-imports.json'),'utf8')).edges;
for(const e of edges){ const f=e.from.replace(/^file:/,''); const t=e.to.replace(/^file:/,''); if(imports.has(f)) imports.get(f).push(t); }
const dirtyDeps={}; for(const p of plan.dirty){ dirtyDeps[p]=(imports.get(p)||[]).filter(q=>dirtySet.has(q)); }
plan.dirty_deps=dirtyDeps; writeFileSync(join(OUT,'plan.json'), JSON.stringify(plan,null,2));
console.log(JSON.stringify({dirty:plan.dirty.length, with_deps:Object.values(dirtyDeps).filter(d=>d.length>0).length},null,2));