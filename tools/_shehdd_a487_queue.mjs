import { readFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const queue=new Set(readFileSync(ROOT+'/dag/watchdog/extra-targets.txt','utf8').split('\n').filter(Boolean));
const prio=new Set(readFileSync(ROOT+'/dag/watchdog/priority-files.txt','utf8').split('\n').filter(Boolean));
for(const n of ['Mzk1FourTriangleSharedActual','Mzk1R4LiteralAssemblyActual','Mzk1Step3115ComparisonActual','Mzk1Step3115WiringActual','Mzk1HullDetStep3115Actual','Mzk1HullDetFourTriangleActual','Mzk1QPilotR4Stage5AlignActual']){
  const f='tmp/sheaf/xif/paper/'+n+'.lean';
  const log=ROOT+'/dag/watchdog/logs/'+f.replace(/\//g,'_')+'.log';
  let err='';
  if(existsSync(log)){ const l=readFileSync(log,'utf8').split('\n').find(x=>x.includes(': error')); err=l?l.trim().slice(0,150):''; }
  console.log(n+' q='+(queue.has(f)?'1':'0')+' p='+(prio.has(f)?'1':'0')+(err?' | ERR '+err:''));
}
