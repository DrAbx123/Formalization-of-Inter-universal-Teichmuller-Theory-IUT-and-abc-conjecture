import { readFileSync, appendFileSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const names=readdirSync(ROOT+'/tmp/sheaf/xif/paper').filter(f=>f.startsWith('Shehdd')&&f.endsWith('.lean')&&!f.includes('Adapted'));
const extra=readFileSync(ROOT+'/dag/watchdog/extra-targets.txt','utf8').split('\n');
const missing=names.map(n=>'tmp/sheaf/xif/paper/'+n).filter(p=>!extra.includes(p));
console.log('not in extras: '+(missing.join(',')||'none'));
for(const p of missing) appendFileSync(ROOT+'/dag/watchdog/extra-targets.txt', p+'\n');
if(missing.length) console.log('added '+missing.length+' to extras');
