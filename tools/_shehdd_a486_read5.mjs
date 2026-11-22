import { readFileSync } from 'node:fs';
const ROOT='D:/lean';
const t=readFileSync(ROOT+'/tmp/sheaf/xif/paper/Mzk1Step3115WiringActual.lean','utf8').split('\n');
for(let i=24;i<78;i++) console.log((i+1)+': '+t[i]);
