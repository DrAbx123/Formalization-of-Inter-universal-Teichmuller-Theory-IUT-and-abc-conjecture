import { readFileSync } from 'node:fs';
const ROOT='D:/lean';
const j=JSON.parse(readFileSync(ROOT+'/dag/GAP-CLOSURE-CANDIDATES.json','utf8'));
const gs=j.groups;
console.log('groups='+Object.keys(gs).length+': '+Object.keys(gs).join(', '));
for(const [name,g] of Object.entries(gs)){
  console.log('=== '+name+' keys='+Object.keys(g).join(','));
  const terms=g.terms||g.term||[];
  console.log('  terms='+JSON.stringify(terms).slice(0,300));
  const counts={}; for(const k of Object.keys(g)){ const v=g[k]; counts[k]=Array.isArray(v)?v.length:(v&&typeof v==='object'?Object.keys(v).length:v); }
  console.log('  stats='+JSON.stringify(counts).slice(0,400));
}
