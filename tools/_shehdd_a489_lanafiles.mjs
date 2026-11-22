import { readFileSync, existsSync, readdirSync, statSync } from 'node:fs';
const ROOT='D:/lean';
const src=ROOT+'/tmp/dsh-oct6-openai-math-survey-20261016/repos/lana/iut/iut-main';
const dirs=['Iut4Sec1','Iut/Implication','Iut/Tripod','Iut/Cor312','Iut/Abc','Iut/Wall','Iut/WallEquiv'];
const queue=new Set(readFileSync(ROOT+'/dag/watchdog/extra-targets.txt','utf8').split('\n').filter(Boolean));
const ver=JSON.parse(readFileSync(ROOT+'/dag/generated/declarations-index.json','utf8')).declarations;
for(const d of dirs){
  const p=src+'/'+d;
  if(!existsSync(p)){ console.log('== '+d+' MISSING'); continue; }
  const files=readdirSync(p).filter(f=>f.endsWith('.lean'));
  console.log('== '+d+' files='+files.length);
  for(const f of files.slice(0,30)){
    const rel=d+'/'+f;
    console.log('   '+rel);
  }
}
