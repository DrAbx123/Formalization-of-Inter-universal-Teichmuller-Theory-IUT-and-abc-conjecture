import { readdirSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const base=ROOT+'/tmp/dsh-oct6-openai-math-survey-20261016/repos/lana';
const spec={'genl':'genl-master/Genl','heights':'heights-main/Heights','tate-curves-theta':'tate-curves-theta-main/TateCurvesTheta','elliptic-curves':'elliptic-curves-main/EllipticCurves','padic-log-volume':'padic-log-volume-main/PadicLogVolume','continuous-kummer-theory':'continuous-kummer-theory-main/ContinuousKummerTheory','belyi':'belyi-main/Belyi','orbicurve-cores':'orbicurve-cores-main/OrbicurveCores','tempered-fundamental-groups':'tempered-fundamental-groups-main/TemperedFundamentalGroups'};
for(const [pkg,rel] of Object.entries(spec)){
  const d=base+'/'+pkg+'/'+rel;
  if(!existsSync(d)){ console.log(pkg+' MISSING'); continue; }
  function walk(x,prefix,acc){ for(const e of readdirSync(x,{withFileTypes:true})){ const p=x+'/'+e.name; if(e.isDirectory()) walk(p,prefix+rel+'/'+e.name+'/',acc); else if(e.name.endsWith('.lean')) acc.push(prefix+rel+'/'+e.name); } return acc; }
  const files=walk(d,'',[]);
  console.log('== '+pkg+' files='+files.length+' : '+files.slice(0,18).join(' | '));
}
