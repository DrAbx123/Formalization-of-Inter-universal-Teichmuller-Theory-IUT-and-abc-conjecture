import { existsSync, readdirSync, statSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/tmp/sheaf/lana';
console.log('lana exists='+existsSync(p));
if(existsSync(p)){
  const dirs=readdirSync(p,{withFileTypes:true}).filter(e=>e.isDirectory()).map(e=>e.name);
  console.log('dirs: '+dirs.join(', '));
  for(const d of dirs){
    let n=0; (function walk(x){ for(const e of readdirSync(x,{withFileTypes:true})){ const q=x+'/'+e.name; if(e.isDirectory()) walk(q); else if(e.name.endsWith('.lean')) n++; } })(p+'/'+d);
    console.log('  '+d+': lean files='+n);
  }
}
console.log('--- original LANA Iut dirs ---');
const lana=ROOT+'/tmp/dsh-oct6-openai-math-survey-20261016/repos/lana/iut/iut-main';
console.log('lana root exists='+existsSync(lana));
if(existsSync(lana)){ const ls=readdirSync(lana); console.log('ls: '+ls.join(', '));
  if(existsSync(lana+'/Iut')){ const iut=readdirSync(lana+'/Iut'); console.log('Iut/: '+iut.slice(0,40).join(', ')); }
}
