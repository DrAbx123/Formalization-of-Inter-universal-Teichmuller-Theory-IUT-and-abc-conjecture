import { readFileSync, writeFileSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const dir=ROOT+'/tmp/sheaf/xif/paper';
const files=readdirSync(dir).filter(f=>f.startsWith('Shehdd')&&f.endsWith('.lean')&&!f.includes('Adapted'));
const extraPath=ROOT+'/dag/watchdog/extra-targets.txt';
let cur=readFileSync(extraPath,'utf8');
const lines=cur.split('\n');
const have=new Set(lines.filter(Boolean));
let added=0;
for(const f of files){ const rel='tmp/sheaf/xif/paper/'+f; if(!have.has(rel)){ lines.push(rel); have.add(rel); added++; } }
writeFileSync(extraPath, lines.filter((l,i)=>!(l===''&&i===lines.length-1)).join('\n')+'\n');
console.log('my non-adapted files='+files.length+' newly added to extras='+added+' total extra lines='+have.size);
