import { readFileSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const dir=ROOT+'/dag/watchdog/logs';
const files=readdirSync(dir).filter(f=>f.includes('Shehdd')&&f.endsWith('.lean.log'));
const errs={};
for(const f of files){
  const txt=readFileSync(dir+'/'+f,'utf8');
  const lines=txt.split('\n').filter(l=>l.includes(': error:'));
  if(lines.length){ errs[f.replace('.lean.log','.lean')]=lines.slice(0,4); }
}
console.log('logs with errors: '+Object.keys(errs).length+' / '+files.length);
for(const [f,ls] of Object.entries(errs)){ console.log('--- '+f); for(const l of ls) console.log('   '+l.trim().slice(0,240)); }
