import { readFileSync, writeFileSync, existsSync, statSync, mkdirSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
const ROOT='D:/lean'; const OUT=join(ROOT,'dag','watchdog'); mkdirSync(OUT,{recursive:true});
const dag=JSON.parse(readFileSync(join(ROOT,'dag','declaration-dag.json'),'utf8'));
const exits=new Map(); try{ for(const line of readFileSync(join(ROOT,'tmp','xif_guarded_results.log'),'utf8').split(/\r?\n/)){ const m=line.match(/^EXIT=(-?\d+) FILE=(\S+)/); if(m) exits.set(m[2].replaceAll('\\','/'),Number(m[1])); } }catch{}
const portedPrefix=ROOT+'/tmp/external/ported/';
const oleanCands=(p)=>{ const cands=[]; const rel=p.replace(/\.lean$/,'');
  if(p.startsWith(portedPrefix)){ const rest=p.slice(portedPrefix.length); const pkg=rest.split('/')[0]; const pkgRoot=portedPrefix+pkg+'/'; const modRel=p.slice(pkgRoot.length).replace(/\.lean$/,''); cands.push(join(ROOT,'.lake','build','lib','lean',modRel+'.olean')); }
  cands.push(join(ROOT,'.lake','build','lib','lean',rel+'.olean')); return cands; };
const suspectSorry=(file)=>{ try{ const tx=readFileSync(join(ROOT,file),'utf8'); const lines=tx.split(/\r?\n/); let hits=0; for(const raw of lines){ const line=raw.replace(/--.*$/,''); if(!/\bsorry\b/.test(line)) continue; if(/no sorry|without sorry|NO sorry|contains NO|No sorry/i.test(raw)) continue; if(/(:=|exact|\bby\b|\bapply\b|⊢|·|;|\bsorry\s*\)|\bsorry\s*$)/.test(line)) hits++; } return hits; }catch{ return 0; } };
const nodes=[]; let mismatches=[];
for(const n of dag.nodes){ const files=(n.files||[]).filter(f=>f.endsWith('.lean')&&existsSync(join(ROOT,f)));
  const ev=[]; for(const f of files){ const srcM=statSync(join(ROOT,f)).mtimeMs; const susp=suspectSorry(f); let olean=null; for(const c of oleanCands(f)) if(existsSync(c)){ const om=statSync(c).mtimeMs; if(olean===null||om>olean) olean=om; } const exit=exits.has(f)?exits.get(f):null; ev.push({file:f, olean_fresh: !!(olean&&olean>=srcM), last_exit:exit, suspect_sorry:susp}); }
  const oleanGroundTruth = n.evidence==='olean' || String(n.id).startsWith('olean:');
  const allFresh=ev.length>0&&ev.every(e=>e.olean_fresh); const exitsOk=oleanGroundTruth?true:ev.every(e=>e.last_exit===0); const noSuspect=oleanGroundTruth?true:ev.every(e=>(e.suspect_sorry||0)===0);
  const claimed=['PROVED','BOTTOM'].includes(n.status); const mismatch=claimed&&!(allFresh&&exitsOk&&noSuspect);
  const rec={id:n.id,kind:n.kind,status:n.status,files:files.length,all_fresh:allFresh,exits_ok:exitsOk,no_suspect_sorry:noSuspect,mismatch,evidence:ev.slice(0,4)}; nodes.push(rec);
  if(mismatch) mismatches.push(rec); }
const summary={total:nodes.length,mismatch:mismatches.length,proved_like:nodes.filter(n=>['PROVED','BOTTOM'].includes(n.status)).length,fresh_ok:nodes.filter(n=>n.all_fresh&&n.exits_ok).length};
writeFileSync(join(OUT,'runtime-status.json'), JSON.stringify({generated_at:new Date().toISOString(),summary,nodes,mismatches},null,2));
const lines=['# DAG runtime status (watchdog-maintained)','','generated: '+new Date().toISOString(),'','| metric | value |','|---|---|'];
for(const [k,v] of Object.entries(summary)) lines.push('| '+k+' | '+v+' |');
lines.push('','## PROVED/BOTTOM nodes failing freshness/exit/integrity evidence','');
if(!mismatches.length) lines.push('none'); else for(const m of mismatches){ lines.push('- **'+m.id+'** ('+m.status+'): files='+m.files+' all_fresh='+m.all_fresh+' exits_ok='+m.exits_ok); for(const e of m.evidence) lines.push('  - `'+e.file+'` fresh='+e.olean_fresh+' exit='+e.last_exit+' suspect_sorry='+(e.suspect_sorry||0)); }
writeFileSync(join(OUT,'RUNTIME-MISMATCH.md'), lines.join('\n'));
console.log(JSON.stringify(summary,null,2));
for(const m of mismatches.slice(0,8)) console.log('MISMATCH: '+m.id);