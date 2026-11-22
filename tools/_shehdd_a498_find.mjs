import { readFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const names=['AbsTopIII09ThetaHullScalingActual','S3137ThetaHullVolumeScalingActual','GlobalThetaPilotLogVolumeActual','GlobalPositiveThetaHullLogVolumeActual'];
for(const n of names){
  let path=null;
  for(const dir of ['tmp/sheaf/xif/paper','tmp/sheaf/xif','LeanFormal']){
    const cand=ROOT+'/'+dir+'/'+n+'.lean';
    if(existsSync(cand)){ path=cand; break; }
  }
  if(!path){ console.log('MISS '+n); continue; }
  const ole=existsSync(ROOT+'/.lake/build/lib/lean/'+path.replace(ROOT+'/','').replace(/\.lean$/,'.olean'));
  const t=readFileSync(path,'utf8').split('\n');
  console.log('===== '+n+' src='+path.replace(ROOT+'/','')+' olean='+ole+' lines='+t.length);
  for(let i=0;i<t.length;i++){ if(/^(structure|def|abbrev|theorem|lemma|noncomputable def) /.test(t[i])){ let s=t[i].trim(); let j=i+1; while(j<t.length&&j<i+10&&!/:=|where/.test(t[j])){ s+=' '+t[j].trim(); j++; } console.log('  L'+(i+1)+': '+s.slice(0,300)); } }
}
