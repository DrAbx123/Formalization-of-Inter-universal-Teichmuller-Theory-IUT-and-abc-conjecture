import { readFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const base=ROOT+'/tmp/sheaf/lana/iut/Iut';
const queue=new Set(readFileSync(ROOT+'/dag/watchdog/extra-targets.txt','utf8').split('\n').filter(Boolean));
const files=['Wall/QPilotRegion.lean','Wall/Scaling.lean','Wall/IdentifiedCopies.lean','Wall/Pilots.lean','Wall/Constraints.lean','Wall/MultiConstraints.lean','Wall/MultiContainer.lean','Wall/Ind3.lean','Wall/BPS.lean','Wall/Rss.lean','Wall/Checks.lean','Wall/EtaAlg.lean','WallEquiv/Basic.lean','WallEquiv/Gap.lean','WallEquiv/NonDerivable.lean','WallEquiv/Forms.lean','WallEquiv/VcI.lean'];
for(const rel of files){
  const f=base+'/'+rel;
  if(!existsSync(f)){ console.log('MISS '+rel); continue; }
  const olean=existsSync(ROOT+'/.lake/build/lib/lean/tmp/sheaf/lana/iut/Iut/'+rel.replace(/\.lean$/,'.olean'));
  const que=queue.has('tmp/sheaf/lana/iut/Iut/'+rel);
  const t=readFileSync(f,'utf8').split('\n'); const names=[];
  for(let i=0;i<t.length;i++){ if(/^(theorem|def|structure|abbrev|lemma|noncomputable def|noncomputable abbrev) /.test(t[i])) names.push(t[i].trim().split(/\s+/).pop()); }
  console.log('== '+rel+' olean='+olean+' queued='+que+' decls='+names.length);
  console.log('   '+names.slice(0,18).join(', '));
}
