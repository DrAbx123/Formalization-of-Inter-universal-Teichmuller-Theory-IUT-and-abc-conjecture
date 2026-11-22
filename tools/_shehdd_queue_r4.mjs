import { readFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const rel='tmp/sheaf/xif/paper/ShehddFourTriangleAssemblyActual.lean';
const txt=readFileSync(ROOT+'/dag/watchdog/extra-targets.txt','utf8');
if(!txt.split('\n').includes(rel)){ appendFileSync(ROOT+'/dag/watchdog/extra-targets.txt', rel+'\n'); console.log('queued '+rel); } else console.log('already queued');
