import { readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const ROOT='D:/lean'; const T=join(ROOT,'papers','motizuki_corpus','text');
const files=readdirSync(T).filter(f=>f.endsWith('.txt'));
const out=[];
for(const f of files){
  const src=readFileSync(join(T,f),'utf8');
  const sect=[...src.matchAll(/^\s*§\s*([0-9]+(?:\.[0-9]+)?)\.?\s+([^\n]{0,80})/gm)].map(m=>({sec:m[1], title:m[2].trim()}));
  const thm=[...src.matchAll(/(Theorem|Corollary|Cor\.|Proposition|Lemma|Definition|Def\.)\s+([0-9]+\.[0-9]+(?:\.[0-9]+)?)/g)].map(m=>({kind:m[1], num:m[2]}));
  const uniq={}; for(const t of thm){ const k=t.kind+' '+t.num; uniq[k]=(uniq[k]||0)+1; }
  out.push({ file:f, size:src.length, section_count:sect.length, sections:sect.slice(0,60), theorem_like_count:Object.keys(uniq).length, theorem_like:Object.keys(uniq).slice(0,120) });
}
writeFileSync(join(ROOT,'coord','PAPER-INDEX.json'), JSON.stringify({ generated_by:'tools/paper_index.mjs', paper_count:out.length, papers:out }, null, 0));
console.log(JSON.stringify(out.slice(0,8).map(o=>({file:o.file, sections:o.section_count, thms:o.theorem_like_count})), null, 2));
console.log('total papers: '+out.length);