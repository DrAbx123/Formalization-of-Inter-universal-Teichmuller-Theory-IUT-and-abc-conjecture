import { readFileSync, writeFileSync, existsSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const PAPER=ROOT+'/tmp/sheaf/xif/paper';
const lines=readFileSync(ROOT+'/tmp/xif_guarded_results.log','utf8').split('\n');
const latest=(rel)=>{ for(let i=lines.length-1;i>=0;i--){ if(lines[i].includes('FILE='+rel)) return lines[i]; } return null; };
const probeState=new Map();
for(const l of lines){ const m=l.match(/^EXIT=(\d+) FILE=(tmp\/sheaf\/xif\/paper\/[^\s]*[Pp]robe[^\s]*\.lean)/); if(m) probeState.set(m[2],m[1]); }
const all=readdirSync(PAPER);
const plain=all.filter(f=>f.endsWith('.lean')&&!f.startsWith('_')).map(f=>f.replace(/\.lean$/,''));
const rows=[];
for(const [p,st] of probeState){
  const exists=existsSync(ROOT+'/'+p);
  if(exists) continue;
  const stem=p.split('/').pop().replace(/\.lean$/,'');
  const clean=stem.replace(/^_/,'').replace(/Probe/g,'').replace(/\d+$/,'').replace(/_+$/,'');
  const cands=plain.filter(b=>clean.length>2 && (b.startsWith(clean)||clean.startsWith(b)||b.includes(clean))).sort((a,b)=>b.length-a.length);
  let src=null, srcResult=null;
  for(const b of cands){ const rel='tmp/sheaf/xif/paper/'+b+'.lean'; const lr=latest(rel); if(!src){ src=b; srcResult=lr; } if(lr&&lr.includes('EXIT=0')){ src=b; srcResult=lr; break; } }
  rows.push({probe:p, stem, lastExit:st, exists, source:src, sourceGreen: !!(srcResult&&srcResult.includes('EXIT=0'))});
}
const rebuiltNames=['_AutoProbe_Mzk1StepVPaperActual','_AutoProbe_Mzk1Cor312TargetWiringActual','_AutoProbe_Mzk1IUTIIILinkActual','_AutoProbe_Mzk1KummerThetaInterfaceActual','_AutoProbe_Mzk1G2CDConsumerActual','_AutoProbe_Mzk1R9PointMembershipConsumerActual','_AutoProbe_Mzk1GeomCoreFiniteMapChartInterfaceActual','_AutoProbe_Mzk1GeomCoreLineBundleInterfaceActual','_AutoProbe_Mzk1Thm110SlackActual','_AutoProbe_Mzk1E5UniformHeightActual','_AutoProbe_Mzk1Prop58iConcreteActual','_AutoProbe_Mzk1StepXIContractConstructionActual','_AutoProbe_Mzk1Cor312ObligationConsumerActual','_AutoProbe_Mzk1R9HullConsumerActual','_AutoProbe_Hull13TwoSidedBoundActual','_AutoProbe_AbsTopIII05Section0ObjectsActual'];
const md=[];
md.push('# PROBE-AUDIT — 2026-11-11 (shehdd A465 probe cleanup audit)');
md.push('');
md.push('**Trigger**: during A465 probe-infra maintenance the incremental script additionally deleted 1849 probe files whose source latest result was non-EXIT0 or missing (most had never been compiled / had no results record).');
md.push('');
md.push('**New rule (effective now)**: probe generator is APPEND-ONLY - only create probes for latest-EXIT0 sources without a probe; NO DELETION of probe files. extra-targets only dedupe/sort/append. This audit + the 16 rebuilds are a one-off recovery.');
md.push('');
md.push('## Deleted probes that have results records: 36 (30 last-EXIT0 + 6 last-EXIT1)');
md.push('');
md.push('16 AutoProbe files rebuilt under their original names (source file + first 3 declarations #print axioms); 20 legacy hand-written probes NOT rebuilt.');
md.push('');
md.push('### Rebuilt (16)');
md.push('');
md.push('| probe | last EXIT | rebuilt from |');
md.push('|---|---|---|');
for(const n of rebuiltNames){ const p='tmp/sheaf/xif/paper/'+n+'.lean'; const ex=existsSync(ROOT+'/'+p); const b=n.replace(/^_AutoProbe_/,''); md.push('| '+n+' | '+(probeState.get(p)||'?')+' | '+b+'.lean '+(ex?'rebuilt':'MISSING!')+' |'); }
md.push('');
md.push('### Not rebuilt: legacy hand-written probes (20) and reasons');
md.push('');
md.push('| probe | last EXIT | source candidate | reason |');
md.push('|---|---|---|---|');
for(const r of rows){
  let reason='source candidate non-EXIT0 or absent';
  if(r.source==='Mzk1StepProviderPrimeActual') reason='source currently EXIT1 (actively owned lane)';
  else if(!r.source) reason='old probe name cannot be mapped uniquely to a current source (S1814/S2433/S3127/S3136/HaarBody legacy families)';
  md.push('| '+r.stem+' | '+r.lastExit+' | '+(r.source||'n/a')+' | '+reason+' |');
}
md.push('');
md.push('## Reference check (fragments / notes / pins)');
md.push('');
md.push('- coord/paper-chain/target-chain.route-mentions.json has two DEF route-mention nodes citing _S3136Stage4HostProbe (historical AUDIT_LEDGER line / priority list); these are NOT CITABLE pins and were left untouched.');
md.push('- Main coord/dag fragments, route index and CITABLE pin notes contain NO references to any other deleted probe name (all hits are watchdog generated caches: graph-cache/order/extra-targets).');
md.push('- Conclusion: NO CITABLE pin affected. If a hand-recorded pin referenced one of these probes, provide the file path and the probe can be rebuilt from the node declarations.');
md.push('');
md.push('## Current probe infra state');
md.push('');
md.push('- tmp/sheaf/xif/paper/_AutoProbe_*.lean: 240 files (224 regular + 16 rebuilt).');
md.push('- dag/watchdog/extra-targets.txt: 530 entries (290 non-probe + 240 auto probes), deduped + sorted.');
md.push('- tools/_shehdd_auto_probes.mjs: append-only (no unlink).');
writeFileSync(ROOT+'/coord/PROBE-AUDIT.md', md.join('\n')+'\n');
console.log('PROBE-AUDIT.md written; missing probes='+rows.length);
