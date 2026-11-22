import { readFileSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const files=readdirSync(ROOT+'/coord').filter(f=>/^target-chain\.iut-(skeleton|pre-.*)\.json$/.test(f));
console.log('fragments='+files.join(','));
for(const f of files){
  const j=JSON.parse(readFileSync(ROOT+'/coord/'+f,'utf8'));
  console.log('\n## '+f+' nodes='+(j.nodes||[]).length+' edges='+(j.edges||[]).length);
  for(const n of (j.nodes||[])){
    const fcnt=(n.files||[]).length; const dcount=(typeof n.declarations==='object'&&n.declarations)?Object.values(n.declarations).flat().length:0;
    console.log('NODE|'+n.id+'|'+n.kind+'|'+n.status+'|files='+fcnt+'|decls='+dcount+'|'+(n.title||'').slice(0,60));
  }
}
