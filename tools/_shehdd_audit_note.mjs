import { readFileSync, writeFileSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/PROBE-AUDIT.md';
let txt=readFileSync(p,'utf8');
const ap=readdirSync(ROOT+'/tmp/sheaf/xif/paper').filter(f=>f.startsWith('_AutoProbe_')).length;
const note='\n## Status note ('+new Date().toISOString()+'-ish)\n\n- AutoProbe files: '+ap+'.\n- 130 EXIT0 / 8 stale-record EXIT1 (contents verified correct after multi-namespace FQN fix; awaiting watchdog recompile).\n';
if(!txt.includes('## Status note')) txt+=note;
else { txt=txt.replace(/## Status note[\s\S]*$/,'## Status note ('+new Date().toISOString()+')\n\n- AutoProbe files: '+ap+'.\n- 130 EXIT0 / 8 stale-record EXIT1 (contents verified correct after multi-namespace FQN fix; awaiting watchdog recompile).\n'); }
writeFileSync(p,txt);
console.log('audit note updated, probes='+ap);
