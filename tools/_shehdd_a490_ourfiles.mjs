import { readFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const files=['tmp/sheaf/lana/iut/Iut/Wall/NumericalWallHullActual.lean','tmp/sheaf/lana/iut/Iut/Wall/NumericalWallRssActual.lean'];
const q=new Set(readFileSync(ROOT+'/dag/watchdog/extra-targets.txt','utf8').split('\n').filter(Boolean));
for(const f of files){
  const src=existsSync(ROOT+'/'+f);
  const ole=existsSync(ROOT+'/.lake/build/lib/lean/'+f.replace(/\.lean$/,'.olean'));
  const log='dag/watchdog/logs/'+f.replace(/\//g,'_')+'.log';
  let err='';
  if(existsSync(ROOT+'/'+log)){ const l=readFileSync(ROOT+'/'+log,'utf8').split('\n').find(x=>x.includes(': error')); err=l?l.trim().slice(0,200):''; }
  console.log(f.split('/').pop()+' src='+src+' olean='+ole+' queued='+q.has(f)+(err?' ERR: '+err:''));
}
// check original LANA repo lacks these
const orig='tmp/dsh-oct6-openai-math-survey-20261016/repos/lana/iut/iut-main/Iut/Wall/NumericalWallHullActual.lean';
console.log('exists in original repo='+existsSync(ROOT+'/'+orig));
