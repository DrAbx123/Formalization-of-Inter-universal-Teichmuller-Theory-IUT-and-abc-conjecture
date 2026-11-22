#!/usr/bin/env node
// Show last watchdog event per target: node tools/wd_status.mjs [PATH...] [--err]
import { readFileSync, existsSync } from 'node:fs';
const LOG='D:/lean/dag/watchdog/watchdog.log';
const WL='D:/lean/dag/watchdog/extra-targets.txt';
const norm=p=>p.trim().replaceAll('\\','/').replace(/^D:\/lean\//i,'').replace(/^\.\//,'');
const showErr=process.argv.includes('--err');
const args=process.argv.slice(2).filter(x=>x!=='--err').map(norm);
const last=new Map();
for(const line of readFileSync(LOG,'utf8').split(/\r?\n/)){
  const m=line.match(/^\S+ (START|DONE|FAIL|SKIP|SPAWN ERR|TIMEOUT KILL)\b.*?((?:tmp|LeanFormal|Mathlib|Iut|Belyi)[^ ]*\.lean)/);
  if(m) last.set(norm(m[2]),{verb:m[1],ts:line.split(' ')[0],line});
}
const wl=existsSync(WL)?readFileSync(WL,'utf8').split(/\r?\n/).map(norm).filter(Boolean):[];
for(const p of (args.length?args:wl)){
  const l=last.get(p);
  console.log((l?l.verb+' '+l.ts:'NO-EVENT')+'  '+p);
  if(showErr && l && l.verb==='FAIL'){
    const lp='D:/lean/dag/watchdog/logs/'+p.replace(/[\/\\:]/g,'_')+'.log';
    try{
      const t=readFileSync(lp,'utf8').split(/\r?\n/).filter(Boolean).slice(-12).join('\n');
      console.log('  --- last lines of '+lp+' ---\n'+t.split('\n').map(x=>'  '+x).join('\n'));
    }catch(e){ console.log('  (no log file)'); }
  }
}
