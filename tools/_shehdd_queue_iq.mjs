import { readFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const rels=['tmp/sheaf/xif/paper/GlobalIQHullInterfaceActual.lean','tmp/sheaf/xif/paper/GlobalIQHullThetaPilotActual.lean'];
const txt=readFileSync(ROOT+'/dag/watchdog/extra-targets.txt','utf8');
const have=new Set(txt.split('\n'));
let added=0;
for(const rel of rels){ if(!have.has(rel)){ appendFileSync(ROOT+'/dag/watchdog/extra-targets.txt', rel+'\n'); added++; } }
console.log('queued '+added+' literal IQ carrier files');
