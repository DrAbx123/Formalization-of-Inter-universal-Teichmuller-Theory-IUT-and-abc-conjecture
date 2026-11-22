import { readFileSync, writeFileSync } from 'node:fs';
const p='D:/lean/tools/_shehdd_survey_match.mjs';
let t=readFileSync(p,'utf8');
t=t.replace("import { readFileSync, existsSync, statSync } from 'node:fs';","import { readFileSync, existsSync, statSync, writeFileSync } from 'node:fs';");
t=t.replace("require('fs').writeFileSync(ROOT+'/tmp/_survey_match.json',JSON.stringify(out,null,2));","writeFileSync(ROOT+'/tmp/_survey_match.json',JSON.stringify(out,null,2));");
writeFileSync(p,t);
console.log('patched');
