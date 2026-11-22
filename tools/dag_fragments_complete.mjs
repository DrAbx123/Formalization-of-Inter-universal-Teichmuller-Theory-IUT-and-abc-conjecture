import { readFileSync, writeFileSync, existsSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { join } from 'node:path';
const ROOT='D:/lean';
const rm=readFileSync(join(ROOT,'dag','complete','route-mentions.jsonl'),'utf8').trim().split('\n').filter(Boolean);
const nodes=[]; const seen=new Set();
for(const ln of rm){ const o=JSON.parse(ln); const id='mention:'+createHash('sha1').update(o.source+'|'+o.line).digest('hex').slice(0,12); if(seen.has(id))continue; seen.add(id);
  const files=existsSync(join(ROOT,o.source))?[o.source]:[];
  nodes.push({ id, kind:'route_mention', title:o.text.slice(0,120), status:'DEF', files, declarations:{}, note:'line '+o.line+': '+o.text.slice(0,300) }); }
writeFileSync(join(ROOT,'coord','target-chain.route-mentions.json'), JSON.stringify({ nodes, edges: [] }));
const pl=readFileSync(join(ROOT,'dag','complete','paper-labels.jsonl'),'utf8').trim().split('\n').filter(Boolean);
const pnodes=[]; const pseen=new Set();
for(const ln of pl){ const o=JSON.parse(ln); const id='plabel:'+o.paper.replace(/[^A-Za-z0-9]/g,'_').slice(0,40)+':'+o.kind+':'+o.label+':'+o.line; if(pseen.has(id))continue; pseen.add(id);
  const f='papers/motizuki_corpus/text/'+o.paper;
  pnodes.push({ id, kind:'paper_label', title:o.kind+' '+o.label, status:'DEF', files:[f], declarations:{}, note:'paper label '+o.kind+' '+o.label+' at line '+o.line }); }
writeFileSync(join(ROOT,'coord','target-chain.paper-labels.json'), JSON.stringify({ nodes:pnodes, edges: [] }));
console.log(JSON.stringify({route_mentions:nodes.length, paper_labels:pnodes.length},null,2));