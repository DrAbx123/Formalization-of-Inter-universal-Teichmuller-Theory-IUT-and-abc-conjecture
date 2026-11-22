#!/usr/bin/env node
// Append targets to the watchdog whitelist with retry+dedupe: node tools/wd_add.mjs PATH...
import { readFileSync, writeFileSync, existsSync, renameSync } from 'node:fs';
const F='D:/lean/dag/watchdog/extra-targets.txt';
const norm=p=>p.trim().replaceAll('\\','/').replace(/^D:\/lean\//i,'').replace(/^\.\//,'');
const sleep=ms=>new Promise(r=>setTimeout(r,ms));
const main=async()=>{
  const add=process.argv.slice(2).map(norm).filter(Boolean);
  if(!add.length){ console.log(JSON.stringify({added:0})); return; }
  for(let i=0;i<60;i++){
    try{
      const cur=existsSync(F)?readFileSync(F,'utf8').split(/\r?\n/).map(x=>x.trim()).filter(Boolean):[];
      const set=new Set(cur); let added=0;
      for(const a of add) if(!set.has(a)){ set.add(a); added++; }
      const tmp=F+'.tmp-'+process.pid;
      writeFileSync(tmp,[...set].join('\n')+(set.size?'\n':''));
      renameSync(tmp,F);
      console.log(JSON.stringify({added,total:set.size,files:add}));
      return;
    }catch(e){ await sleep(120); }
  }
  console.error('wd_add: failed after retries'); process.exit(1);
};
main();
