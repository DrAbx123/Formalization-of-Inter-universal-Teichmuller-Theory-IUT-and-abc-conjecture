import { readFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const base=ROOT+'/tmp/sheaf/lana/iut/Iut';
const files=['Wall/Rss.lean','Wall/QPilotRegion.lean','Wall/Scaling.lean','Wall/IdentifiedCopies.lean','Wall/Pilots.lean','Wall/Ind3.lean','WallEquiv/Basic.lean','WallEquiv/Gap.lean','WallEquiv/NonDerivable.lean'];
function nameOf(line){ let s=line.replace(/^\s*(noncomputable\s+)?(private\s+)?(protected\s+)?(theorem|lemma|def|structure|abbrev|instance|noncomputable def|noncomputable abbrev)\s+/,'').trim(); const m=s.match(/^([A-Za-z_][A-Za-z0-9_'’.]*)/); return m?m[1]:'?'; }
for(const rel of files){
  const f=base+'/'+rel; if(!existsSync(f)){ console.log('MISS '+rel); continue; }
  const t=readFileSync(f,'utf8').split('\n'); const names=[];
  for(let i=0;i<t.length;i++){ if(/^\s*(noncomputable\s+)?(theorem|lemma|def|structure|abbrev|instance)\s/.test(t[i])) names.push(nameOf(t[i])+'@'+(i+1)); }
  console.log('== '+rel+' decls='+names.length);
  console.log('   '+names.slice(0,50).join(', '));
}
