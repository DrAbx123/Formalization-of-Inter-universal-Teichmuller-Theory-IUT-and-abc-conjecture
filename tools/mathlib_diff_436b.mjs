import { readFileSync, readdirSync } from 'node:fs';
import { join, relative } from 'node:path';
const ROOT='D:/lean';
function walk(d,out){ let e=[]; try{e=readdirSync(d,{withFileTypes:true})}catch{ return out; } for(const x of e){ if(x.name==='.lake'||x.name==='.git') continue; const p=join(d,x.name); if(x.isDirectory()) walk(p,out); else if(x.name.endsWith('.lean')) out.push(p); } return out; }
const A=walk(join(ROOT,'.lake/packages/mathlib/Mathlib'),[]).map(f=>relative(join(ROOT,'.lake/packages/mathlib'),f).replace(/\\/g,'/'));
const B=walk(join(ROOT,'tmp/mathlib4-4.36.0-rc2/Mathlib'),[]).map(f=>relative(join(ROOT,'tmp/mathlib4-4.36.0-rc2'),f).replace(/\\/g,'/'));
const setA=new Set(A); const newFiles=B.filter(f=>!setA.has(f));
console.log('new',newFiles.length);
const majors=['Mathlib/NumberTheory','Mathlib/MeasureTheory','Mathlib/Analysis','Mathlib/AlgebraicGeometry','Mathlib/RingTheory','Mathlib/FieldTheory','Mathlib/CategoryTheory','Mathlib/Topology','Mathlib/LinearAlgebra','Mathlib/SetTheory','Mathlib/Combinatorics','Mathlib/Geometry'];
for(const m of majors){ const hits=newFiles.filter(f=>f.startsWith(m+'/')); if(hits.length){ console.log('## '+m+' new='+hits.length); for(const h of hits) console.log('  '+h); } }