import { spawnSync } from 'node:child_process';
import { existsSync, mkdirSync, writeFileSync, readFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
const ROOT='D:/lean';
const args=process.argv.slice(2);
let files=args;
if(args.length===1 && args[0].endsWith('.txt')){ files=readFileSync(join(ROOT,args[0]),'utf8').split(/\r?\n/).map(s=>s.trim()).filter(Boolean); }
if(!files.length){ console.log('usage: node gate_check.mjs <file...> | <list.txt>'); process.exit(9); }
const rows=[];
for(const f of files){
  const rel=f.replaceAll('\\','/');
  const mod=rel.replace(/\.lean$/,'');
  const olean=join(ROOT,'.lake','build','lib','lean',mod+'.olean');
  mkdirSync(dirname(olean),{recursive:true});
  const r=spawnSync('lake',['env','lean','-R',ROOT,'-o',olean,join(ROOT,rel)],{cwd:ROOT,encoding:'utf8',timeout:600000,maxBuffer:64*1024*1024});
  const out=((r.stdout||'')+(r.stderr||''));
  const errLine=(out.split('\n').find(l=>l.includes(': error'))||'').trim().slice(0,200);
  const axiomLines=out.split('\n').filter(l=>l.includes('depends on axioms')||l.includes('does not depend on any axioms'));
  let gate='NONE';
  if(axiomLines.length){
    if(axiomLines.some(l=>/depends on axioms:(?!.*propext)/.test(l) || /sorryAx|Classical\.choice\.add|ofReduceBool/.test(l))) gate='BAD';
    else if(axiomLines.some(l=>l.includes('Classical.choice'))) gate='TRIO';
    else if(axiomLines.every(l=>l.includes('does not depend'))) gate='CLEAN';
    else gate='CHECK';
  }
  const ok=(r.status===0 && existsSync(olean));
  rows.push({file:rel, exit:r.status===null?'TIME':r.status, olean:existsSync(olean), gate, gates:axiomLines.length, err:errLine});
  console.log(JSON.stringify(rows[rows.length-1]));
}
const csv=['file,exit,olean,gate,gate_lines,first_error'].concat(rows.map(r=>[r.file,r.exit,r.olean,r.gate,r.gates,'"'+r.err.replaceAll('"','""')+'"'].join(','))).join('\n');
writeFileSync(join(ROOT,'tmp','gate_check_results.csv'),csv,'utf8');
console.log('CSV tmp/gate_check_results.csv rows='+rows.length);