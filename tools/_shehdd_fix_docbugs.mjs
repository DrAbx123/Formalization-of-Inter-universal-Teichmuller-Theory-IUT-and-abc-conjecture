import { readFileSync, writeFileSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const dir=ROOT+'/tmp/sheaf/xif/paper';
const files=readdirSync(dir).filter(f=>f.startsWith('Shehdd')&&f.endsWith('.lean')&&!f.includes('Adapted'));
let fixedDoc=0; const fixedFiles=[];
for(const f of files){
  const p=dir+'/'+f;
  const lines=readFileSync(p,'utf8').split('\n');
  // find first non-empty non-import line
  let i=0; while(i<lines.length && (lines[i].trim()===''||lines[i].startsWith('import '))) i++;
  if(i<lines.length && lines[i].trim()==='/--'){
    lines[i]='/-!';
    writeFileSync(p, lines.join('\n'));
    fixedDoc++; fixedFiles.push(f);
  }
}
console.log('fixed /-- -> /-! in '+fixedDoc+' files');
console.log(fixedFiles.join(','));
