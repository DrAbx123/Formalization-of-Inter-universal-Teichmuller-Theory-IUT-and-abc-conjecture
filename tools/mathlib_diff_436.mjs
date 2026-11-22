import { readFileSync, readdirSync } from 'node:fs';
import { join, relative } from 'node:path';
const ROOT='D:/lean';
function walk(d,out){ let e=[]; try{e=readdirSync(d,{withFileTypes:true})}catch{ return out; } for(const x of e){ if(x.name==='.lake'||x.name==='.git') continue; const p=join(d,x.name); if(x.isDirectory()) walk(p,out); else if(x.name.endsWith('.lean')) out.push(p); } return out; }
const A=walk(join(ROOT,'.lake/packages/mathlib/Mathlib'),[]);
const B=walk(join(ROOT,'tmp/mathlib4-4.36.0-rc2/Mathlib'),[]);
const relA=new Set(A.map(f=>relative(join(ROOT,'.lake/packages/mathlib'),f)));
const relB=new Set(B.map(f=>relative(join(ROOT,'tmp/mathlib4-4.36.0-rc2'),f)));
const newFiles=[...relB].filter(f=>!relA.has(f));
const goneFiles=[...relA].filter(f=>!relB.has(f));
console.log('A(4.32.2)',relA.size,'B(4.36rc2)',relB.size,'new',newFiles.length,'gone',goneFiles.length);
const byDir={}; for(const f of newFiles){ const d=f.split('/').slice(0,2).join('/'); byDir[d]=(byDir[d]||0)+1; }
console.log('--- new by top dir ---');
for(const [d,c] of Object.entries(byDir).sort((a,b)=>b[1]-a[1]).slice(0,40)) console.log(c,d);
const kw=[['PNT/Chebyshev',/PrimeCounting|Chebyshev|PrimeNumber|PnT/i],['Height/ABC',/Height|ABC|Conductor|Radical|Frey|Szpiro|Elliptic|Weierstrass/i],['Theta/Kummer/Anab',/Theta|Kummer|Anabelian|Belyi|Dessin/i],['Haar/MeasureLog',/Haar|Lebesgue|Measure.*Log|LogVolume/i],['Different/Dedekind',/Different|Dedekind|Disk|Conductor/i],['RiemannRoch',/RiemannRoch|DivisorClassGroup|SerreDuality/i],['Padic/Log',/Padic.*Log|log|Log/i]];
for(const [n,re] of kw){ const hits=newFiles.filter(f=>re.test(f)); console.log('## '+n+' hits='+hits.length); for(const h of hits.slice(0,15)) console.log('  '+h); }