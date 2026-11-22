import { readFileSync, readdirSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const dir=ROOT+'/tmp/sheaf/xif/paper';
const files=readdirSync(dir).filter(f=>f.startsWith('Shehdd')&&f.endsWith('.lean')&&!f.includes('Adapted'));
const miss=[];
for(const f of files){
  const txt=readFileSync(dir+'/'+f,'utf8');
  const imps=txt.split('\n').filter(l=>l.startsWith('import ')).map(l=>l.slice(7).trim());
  for(const imp of imps){
    let rel;
    if(imp.startsWith('tmp.sheaf.xif.paper.')) rel='tmp/sheaf/xif/paper/'+imp.slice('tmp.sheaf.xif.paper.'.length).replace(/\./g,'/')+'.lean';
    else if(imp.startsWith('LeanFormal.')) rel=imp.replace(/\./g,'/')+'.lean';
    else continue;
    const olean=rel.replace(/\.lean$/,'.olean');
    if(existsSync(ROOT+'/'+rel) && !existsSync(ROOT+'/.lake/build/lib/lean/'+olean)) miss.push(f+' -> '+rel);
  }
}
console.log('files with missing-olean imports: '+miss.length);
for(const m of miss) console.log('  '+m);
