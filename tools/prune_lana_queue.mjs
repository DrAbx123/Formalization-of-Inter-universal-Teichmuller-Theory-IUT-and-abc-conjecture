import { readFileSync, writeFileSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
const ROOT='D:/lean';
const files=[]; function walk(d,o){let e=[];try{e=readdirSync(d,{withFileTypes:true})}catch{return o}for(const x of e){const p=d+'/'+x.name;if(x.isDirectory())walk(p,o);else if(x.name.endsWith('.lean'))o.push(p)}return o}; walk(ROOT+'/tmp/sheaf/lana',files);
const mod2file=new Map(); for(const f of files){ const rel=f.replace(ROOT+'/','').replace(/\.lean$/,'').replace(/\//g,'.'); mod2file.set(rel,f); }
const importRe=/^\s*import\s+([A-Za-z0-9_.']+)/gm;
const targets=['tmp.sheaf.lana.iut.Iut.Implication.ChebyshevExplicit','tmp.sheaf.lana.iut.Iut.Implication.PrimeSelection','tmp.sheaf.lana.iut.Iut.Implication.Invariants','tmp.sheaf.lana.iut.Iut.Concrete.LocalEstimate','tmp.sheaf.lana.iut.Iut4Sec1.Basic','tmp.sheaf.lana.iut.Iut4Sec1.WeightedAverage','tmp.sheaf.lana.iut.Iut4Sec1.ArithmeticDivisor'];
const seen=new Set(); const stack=[...targets];
while(stack.length){ const m=stack.pop(); if(seen.has(m)) continue; seen.add(m); const f=mod2file.get(m); if(!f) continue; let s=''; try{ s=readFileSync(f,'utf8'); }catch{ continue; } let mm; while((mm=importRe.exec(s))){ const im=mm[1]; if(im.startsWith('Mathlib')) continue; if(!mod2file.has(im)) continue; if(!seen.has(im)) stack.push(im); } }
const keep=new Set([...seen].map(m=>mod2file.get(m).replace(ROOT+'/','')));
console.log('useful closure', keep.size);
const etPath=ROOT+'/dag/watchdog/extra-targets.txt';
const lines=readFileSync(etPath,'utf8').split(/\r?\n/).filter(Boolean);
const kept=lines.filter(l=>!l.startsWith('tmp/sheaf/lana/')||keep.has(l));
const removed=lines.filter(l=>l.startsWith('tmp/sheaf/lana/')&&!keep.has(l));
writeFileSync(etPath, kept.join('\n')+'\n');
writeFileSync(ROOT+'/tmp/lana_pruned_queue.txt', removed.join('\n')+'\n');
writeFileSync(ROOT+'/tmp/lana_useful_closure.txt', [...keep].join('\n')+'\n');
console.log('queue',lines.length,'->',kept.length,'removed lana',removed.length);