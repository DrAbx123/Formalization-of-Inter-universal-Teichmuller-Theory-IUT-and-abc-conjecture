import { readFileSync, existsSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const cdir=ROOT+'/tmp/sheaf/lana/iut/Iut/Concrete';
for(const f of readdirSync(cdir).filter(x=>x.endsWith('.lean')).sort()){
  const t=readFileSync(cdir+'/'+f,'utf8').split('\n');
  const structs=[];
  for(let i=0;i<t.length;i++){ if(/^(structure|inductive|class) /.test(t[i])) structs.push(t[i].trim().split(/\s+/).slice(0,2).join(' ')+'@'+(i+1)); }
  if(structs.length) console.log(f+': '+structs.join(', '));
}
