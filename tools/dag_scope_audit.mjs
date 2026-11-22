// Audit the prerequisite closure: start from LeanFormal/IUT + target ABC modules, walk imports, report statuses/sorries/axioms.
import { readFileSync, writeFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const d=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const nodes=new Map(); for(const n of d.nodes) nodes.set(n.id,n);
const imports=new Map(); for(const e of d.edges) { if(!imports.has(e.from)) imports.set(e.from,[]); imports.get(e.from).push(e.to); }
const targets=[]; for(const n of d.nodes){ const f=(n.files&&n.files[0])||''; if(f.startsWith('LeanFormal/IUT/')||f.startsWith('Iut/')) targets.push(n.id); }
const closure=new Set(); const stack=[...targets];
while(stack.length){ const id=stack.pop(); if(closure.has(id)) continue; closure.add(id); for(const q of (imports.get(id)||[])) if(!closure.has(q)) stack.push(q); }
let proved=0,gap=0,cond=0,other=0,sorryModules=0,sorryOcc=0, customAxiomModules=0; const gapList=[], bad=[];
const stripComments=(s)=>{ let out=''; let i=0; const n=s.length; while(i<n){ if(s.startsWith('/-',i)){ let depth=1; i+=2; while(i<n && depth>0){ if(s.startsWith('/-',i)){ depth++; i+=2; } else if(s.startsWith('-/',i)){ depth--; i+=2; } else i++; } continue; } if(s.startsWith('--',i)){ const j=s.indexOf('\n',i); i=(j<0?n:j); continue; } if(s[i]==='"'){ i++; while(i<n){ if(s[i]==='\\'){ i+=2; continue; } if(s[i]==='"'){ i++; break; } i++; } out+=' '; continue; } out+=s[i]; i++; } return out; };
const axiomRe=/^\s*(?:unsafe\s+)?axiom\s+([A-Za-z0-9_'.]+)/gm;
for(const id of closure){ const n=nodes.get(id); if(!n) continue; if(n.status==='PROVED') proved++; else if(n.status==='GAP') { gap++; gapList.push(n.files[0]); } else if(n.status==='CONDITIONAL') { cond++; bad.push((n.files[0]||'')+' sorry='+n.sorry_count); } else other++; if(n.sorry_count>0){ sorryModules++; sorryOcc+=n.sorry_count; } const f=(n.files&&n.files[0])||''; if(f && !f.startsWith('tmp/external')){ try{ const raw=readFileSync(ROOT+'/'+f,'utf8'); const s=stripComments(raw); let m; axiomRe.lastIndex=0; let found=0; while((m=axiomRe.exec(s))) found++; if(found>0){ customAxiomModules++; if(bad.length<20) bad.push(f+' axioms='+found); } }catch{} } }
const meta={generated_at:new Date().toISOString(), targets:targets.length, closure:closure.size, proved, gap, conditional:cond, other, sorry_modules_in_closure:sorryModules, sorry_occurrences_in_closure:sorryOcc, modules_with_axiom_declarations:customAxiomModules, gap_files:gapList, bad_sample:bad};
writeFileSync(ROOT+'/dag/PREREQ-SCOPE.json', JSON.stringify(meta,null,2));
const md=['# PREREQ SCOPE AUDIT (import closure from LeanFormal/IUT + Iut targets)','','generated: '+meta.generated_at,'','| metric | value |','|---|---|','| target modules | '+meta.targets+' |','| closure modules | '+meta.closure+' |','| PROVED | '+meta.proved+' |','| GAP | '+meta.gap+' |','| CONDITIONAL | '+meta.conditional+' |','| sorry modules in closure | '+meta.sorry_modules_in_closure+' |','| sorry occurrences in closure | '+meta.sorry_occurrences_in_closure+' |','| modules with custom axiom declarations | '+meta.modules_with_axiom_declarations+' |','','## GAP modules in closure',''];
if(gapList.length===0) md.push('none'); else for(const f of gapList) md.push('- '+f);
md.push('','## CONDITIONAL/sorry or axiom modules in closure','');
if(bad.length===0) md.push('none'); else for(const b of bad) md.push('- '+b);
writeFileSync(ROOT+'/dag/PREREQ-SCOPE.md', md.join('\n'));
console.log(JSON.stringify(meta,null,2).slice(0,1500));