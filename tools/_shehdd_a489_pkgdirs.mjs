import { readdirSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const base=ROOT+'/tmp/dsh-oct6-openai-math-survey-20261016/repos/lana';
const spec={'genl':'genl-master','heights':'heights-main','tate-curves-theta':'tate-curves-theta-main','elliptic-curves':'elliptic-curves-main','padic-log-volume':'padic-log-volume-main','continuous-kummer-theory':'continuous-kummer-theory-main','pi1':'pi1-main','belyi':'belyi-main','oka':'oka-main','orbicurve-cores':'orbicurve-cores-main','tempered-fundamental-groups':'tempered-fundamental-groups-main'};
for(const [pkg,dir] of Object.entries(spec)){
  const d=base+'/'+pkg+'/'+dir;
  if(!existsSync(d)){ console.log(pkg+' DIR MISSING '+d); continue; }
  const entries=readdirSync(d,{withFileTypes:true});
  const dirs=entries.filter(e=>e.isDirectory()).map(e=>e.name);
  const files=entries.filter(e=>e.isFile()&&e.name.endsWith('.lean')).map(e=>e.name);
  console.log('== '+pkg+' dirs=['+dirs.join(',')+'] files=['+files.join(',')+']');
}
