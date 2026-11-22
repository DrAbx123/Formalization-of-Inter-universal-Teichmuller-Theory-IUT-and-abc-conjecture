import { readFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const prio=readFileSync(ROOT+'/dag/watchdog/priority-files.txt','utf8').split('\n').filter(Boolean);
const queue=readFileSync(ROOT+'/dag/watchdog/extra-targets.txt','utf8').split('\n').filter(Boolean);
const olean=f=>existsSync(ROOT+'/.lake/build/lib/lean/'+f.replace(/\.lean$/,'.olean'));
console.log('PRIORITY missing olean:');
for(const f of prio) if(!olean(f)) console.log('  '+(existsSync(ROOT+'/'+f)?'src':'NOSRC')+' '+(queue.includes(f)?'[queued]':'[NOT-QUEUED]')+' '+f);
console.log('QUEUE missing olean:');
for(const f of queue) if(!olean(f)) console.log('  '+(existsSync(ROOT+'/'+f)?'src':'NOSRC')+' '+f);
// critical import check: who imports Mzk1LiteralHullDetCompositionActual?
const { execSync } = { execSync: null };
