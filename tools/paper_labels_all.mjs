import { readdirSync, readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { join } from 'node:path';
const ROOT='D:/lean'; const T=join(ROOT,'papers','motizuki_corpus','text'); const OUT=join(ROOT,'dag','complete'); mkdirSync(OUT,{recursive:true});
const files=readdirSync(T).filter(f=>f.endsWith('.txt'));
const re=/(Theorem|Corollary|Proposition|Lemma|Definition|Remark|Def|Prop|Cor|Thm|Rmk|Re[ms])[ .]*([0-9]+\.[0-9]+(?:\.[0-9]+)?|[A-Z](?:\.\d+)?)/g;
const out=[]; let total=0;
for(const f of files){ const src=readFileSync(join(T,f),'utf8'); const lines=src.split(/\r?\n/);
  for(let i=0;i<lines.length;i++){ const line=lines[i]; re.lastIndex=0; let m; while((m=re.exec(line))!==null){ total++; out.push({paper:f,line:i+1,kind:m[1],label:m[2]}); } } }
writeFileSync(join(OUT,'paper-labels.jsonl'), out.map(o=>JSON.stringify(o)).join('\n'));
const byPaper={}; for(const o of out) byPaper[o.paper]=(byPaper[o.paper]||0)+1;
writeFileSync(join(OUT,'paper-labels-summary.json'), JSON.stringify({papers:files.length, labels:out.length, per_paper:byPaper},null,2));
console.log(JSON.stringify({papers:files.length, labels:out.length},null,2));