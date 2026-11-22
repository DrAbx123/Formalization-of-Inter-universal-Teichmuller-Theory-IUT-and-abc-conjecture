import { spawnSync } from 'node:child_process';
import { existsSync, mkdirSync, writeFileSync, readFileSync, appendFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
const ROOT='D:/lean';
const LIST=join(ROOT,'tmp','front_queue.txt');
let files=process.argv.slice(2);
if(!files.length){ try{ files=readFileSync(LIST,'utf8').split(/\r?\n/).map(s=>s.trim()).filter(Boolean); }catch{ files=[]; } }
if(!files.length){ console.log('front queue empty (tmp/front_queue.txt or args)'); process.exit(0); }
const rows=[];
for(const f of files){
  const rel=f.replaceAll('\\','/'); const mod=rel.replace(/\.lean$/,'');
  const olean=join(ROOT,'.lake','build','lib','lean',mod+'.olean'); mkdirSync(dirname(olean),{recursive:true});
  const r=spawnSync('lake',['env','lean','-R',ROOT,'-o',olean,join(ROOT,rel)],{cwd:ROOT,encoding:'utf8',timeout:600000,maxBuffer:64*1024*1024});
  const out=((r.stdout||'')+(r.stderr||''));
  const errLine=(out.split('\n').find(l=>l.includes(': error'))||'').trim().slice(0,240);
  const axiomLines=out.split('\n').filter(l=>l.includes('depends on axioms')||l.includes('does not depend on any axioms'));
  let gate='NONE';
  if(axiomLines.length){
    if(axiomLines.some(l=>/sorryAx|ofReduceBool|Classical\.choice\.add/.test(l) || /depends on axioms:(?!.*propext)/.test(l))) gate='BAD';
    else if(axiomLines.some(l=>l.includes('Classical.choice'))) gate='TRIO';
    else if(axiomLines.every(l=>l.includes('does not depend'))) gate='CLEAN';
    else gate='CHECK';
  }
  const row={file:rel, exit:r.status, olean:existsSync(olean), gate, gates:axiomLines.length, err:errLine};
  rows.push(row); console.log(JSON.stringify(row));
}
const csv=rows.map(r=>[r.file,r.exit,r.olean,r.gate,r.gates,'"'+r.err.replaceAll('"','""')+'"'].join(',')).join('\n')+'\n';
appendFileSync(join(ROOT,'tmp','front_queue_results.csv'),csv,'utf8');
console.log('front done rows='+rows.length);