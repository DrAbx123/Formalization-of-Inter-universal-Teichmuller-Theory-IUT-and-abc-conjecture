import { readdirSync, readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { join, relative } from 'node:path';
const ROOT='D:/lean'; const OUT=join(ROOT,'dag','complete'); mkdirSync(OUT,{recursive:true});
const skip=new Set(['.lake','.git','node_modules','.dsh']);
const docs=[];
function walk(d){ let es; try{es=readdirSync(d,{withFileTypes:true});}catch{return;} for(const e of es){ if(e.name.startsWith('.')||skip.has(e.name))continue; const p=join(d,e.name); if(e.isDirectory())walk(p); else if(e.isFile()&&(e.name.endsWith('.md')||e.name.endsWith('.txt'))) docs.push(p); } }
walk(ROOT);
const kw=/(route|路线|路径|Stage\s*[0-9]|triangle|三角|alternative|替代|attempt|尝试|refut|反例|counterexample|obstruction|障碍|dead[- ]end|死路|失败|fail|blocker|blocked|superseded|取代|abandon|放弃|archive|归档|legacy|遗留|PREPARED|待命|design|设计|strategy|策略|plan|计划|方案|reduction|归约|invalidate|invalid|不可行|可行)/i;
const out=[]; const seen=new Set(); let total=0;
for(const f of docs){ let src=''; try{src=readFileSync(f,'utf8');}catch{continue;} const r=relative(ROOT,f).replaceAll('\\','/');
  const lines=src.split(/\r?\n/); for(let i=0;i<lines.length;i++){ const line=lines[i]; if(line.length<12||line.length>500) continue; if(!kw.test(line)) continue; total++;
    const norm=line.replace(/\s+/g,' ').trim().slice(0,400); if(seen.has(norm)) continue; seen.add(norm); out.push({source:r,line:i+1,text:norm}); } }
writeFileSync(join(OUT,'route-mentions.jsonl'), out.map(o=>JSON.stringify(o)).join('\n'));
writeFileSync(join(OUT,'route-mentions-summary.json'), JSON.stringify({docs_scanned:docs.length, matched_lines:total, deduped:out.length},null,2));
console.log(JSON.stringify({docs_scanned:docs.length, matched_lines:total, deduped:out.length},null,2));