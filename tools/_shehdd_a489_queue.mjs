import { readFileSync, existsSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const q=readFileSync(ROOT+'/dag/watchdog/extra-targets.txt','utf8').split('\n').filter(Boolean);
const lana=q.filter(f=>f.startsWith('tmp/sheaf/lana/'));
const byPkg={};
for(const f of lana){ const p=f.split('/')[3]; byPkg[p]=(byPkg[p]||0)+1; }
console.log('queued lana total='+lana.length);
console.log('by pkg: '+JSON.stringify(byPkg));
console.log('iut queued='+lana.filter(f=>f.startsWith('tmp/sheaf/lana/iut/')).length);
console.log('Iut4Sec1 queued='+lana.filter(f=>f.startsWith('tmp/sheaf/lana/Iut4Sec1/')).length);
console.log('Iut4Sec1 dir exists='+existsSync(ROOT+'/tmp/sheaf/lana/Iut4Sec1'));
const lanaRoot=ROOT+'/tmp/dsh-oct6-openai-math-survey-20261016/repos/lana/iut/iut-main/Iut4Sec1';
if(existsSync(lanaRoot)){ console.log('LANA Iut4Sec1 files: '+readdirSync(lanaRoot).filter(f=>f.endsWith('.lean')).join(', ')); }
