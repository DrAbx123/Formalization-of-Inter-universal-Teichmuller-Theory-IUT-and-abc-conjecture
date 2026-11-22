import { existsSync, appendFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
const ROOT='D:/lean';
const files=['tmp/sheaf/xif/paper/Mzk1OurFrameworkABCActual.lean','tmp/sheaf/xif/paper/Mzk1PaperToClassicalABCActual.lean'];
const done=new Set();
const deadline=Date.now()+180*60*1000;
while(Date.now()<deadline){
  for(const f of files){
    if(done.has(f)) continue;
    if(existsSync(ROOT+'/'+f)){
      const r=spawnSync(process.execPath,['tools/gate_check.mjs',f],{cwd:ROOT,encoding:'utf8',timeout:1800000,maxBuffer:64*1024*1024});
      const out=((r.stdout||'')+(r.stderr||'')).trim();
      appendFileSync(ROOT+'/tmp/new_file_gates.log','=== '+f+' @ '+new Date().toISOString()+'\n'+out+'\n','utf8');
      console.log('GATED '+f); done.add(f);
    }
  }
  if(done.size===files.length) break;
  spawnSync(process.execPath,['-e','setTimeout(()=>{},20000)'],{cwd:ROOT,timeout:30000});
}
console.log('watch finished done='+done.size);