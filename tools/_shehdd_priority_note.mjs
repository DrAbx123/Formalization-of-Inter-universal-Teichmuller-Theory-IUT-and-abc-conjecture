import { readFileSync, writeFileSync, readdirSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/PROBE-AUDIT.md';
let txt=readFileSync(p,'utf8');
const ap=readdirSync(ROOT+'/tmp/sheaf/xif/paper').filter(f=>f.startsWith('_AutoProbe_')).length;
const prio=readFileSync(ROOT+'/dag/watchdog/priority-files.txt','utf8').split('\n').map(x=>x.trim()).filter(Boolean);
const covered=[];
for(const rel of prio){ const b=rel.split('/').pop().replace(/\.lean$/,''); if(existsSync(ROOT+'/tmp/sheaf/xif/paper/_AutoProbe_'+b+'.lean')) covered.push(b); }
const add='\n## Priority-file probes ('+new Date().toISOString()+')\n\n- Generated probe files for green priority files lacking probes: '+(covered.length?covered.join(', '):'none')+'.\n- AutoProbe total: '+ap+'.\n';
if(!txt.includes('## Priority-file probes')) txt+=add;
writeFileSync(p,txt);
console.log('priority appendix added; covered='+covered.length+' probes='+ap);
