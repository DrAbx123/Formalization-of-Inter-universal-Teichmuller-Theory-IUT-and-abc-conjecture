import { readFileSync, writeFileSync, readdirSync, mkdirSync, existsSync, copyFileSync } from 'node:fs';
import { join, dirname, relative } from 'node:path';
const ROOT='D:/lean';
const SRC=join(ROOT,'tmp/dsh-oct6-openai-math-survey-20261016/repos/lana/iut/iut-main/Iut');
const DST=join(ROOT,'tmp/sheaf/lana/Iut');
function walk(d,out){ let e=[]; try{e=readdirSync(d,{withFileTypes:true})}catch{ return out; } for(const x of e){ const p=join(d,x.name); if(x.isDirectory()) walk(p,out); else if(x.name.endsWith('.lean')) out.push(p); } return out; }
const files=walk(SRC,[]);
let copied=0;
for(const f of files){ const rel=relative(SRC,f).replace(/\\/g,'/'); const dst=join(DST,rel); mkdirSync(dirname(dst),{recursive:true}); let s=readFileSync(f,'utf8'); s=s.replace(/^import Iut\./gm,'import tmp.sheaf.lana.Iut.'); writeFileSync(dst,s); copied++; }
console.log('copied',copied,'to',DST);
// compute import closure for targets
const targets=['Implication/ChebyshevExplicit.lean','Implication/PrimeSelection.lean','Implication/Invariants.lean','Concrete/LocalEstimate.lean','Tripod/Height.lean'].map(t=>join(DST,t.replace(/\//g,'\\')));
const moduleOf=(p)=>relative(ROOT, p).replace(/\\/g,'/').replace(/\.lean$/,'').replace(/\//g,'.');
const byModule=new Map(); for(const f of walk(DST,[])) byModule.set(moduleOf(f), f);
const importRe=/^import\s+([A-Za-z0-9_.']+)/gm;
const seen=new Set(); const stack=[...targets];
while(stack.length){ const f=stack.pop(); if(seen.has(f)) continue; seen.add(f); let s=''; try{ s=readFileSync(f,'utf8'); }catch{ continue; } let m; while((m=importRe.exec(s))){ const mod=m[1]; const dep=byModule.get(mod); if(dep && !seen.has(dep)) stack.push(dep); } }
const rel=[...seen].map(f=>relative(ROOT,f).replace(/\\/g,'/')).filter(f=>f.startsWith('tmp/sheaf/lana/'));
writeFileSync(join(ROOT,'tmp','lana_port_closure.txt'), rel.join('\n')+'\n');
console.log('closure', rel.length);