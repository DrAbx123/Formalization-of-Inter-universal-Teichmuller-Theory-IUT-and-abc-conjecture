import { readFileSync, writeFileSync, existsSync, copyFileSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
const ROOT='D:/lean'; const COORD=join(ROOT,'coord');
const frag=join(COORD,'target-chain.zz-qpilot.json');
copyFileSync(frag, frag+'.bak-adapted');
const j=JSON.parse(readFileSync(frag,'utf8'));
const nodes=j.nodes||[], edges=j.edges||[];
const isAdapted=(n)=>Array.isArray(n.files)&&n.files.some(f=>f.endsWith('Adapted.lean')) || String(n.id).includes('QPX.adapted');
const kept=nodes.filter(n=>!isAdapted(n)); const removed=new Set(nodes.filter(isAdapted).map(n=>n.id));
const keptEdges=edges.filter(e=>!removed.has(e.from)&&!removed.has(e.to));
j.nodes=kept; j.edges=keptEdges; j.meta=j.meta||{}; j.meta.adapted_removed=removed.size; j.meta.note=(j.meta.note||'')+' [A478: removed '+removed.size+' *Adapted nodes (files kept on disk, no longer DAG/queue)]';
writeFileSync(frag, JSON.stringify(j,null,2));
console.log('zz-qpilot: nodes',nodes.length,'->',kept.length,'edges',edges.length,'->',keptEdges.length);
// prune cross-fragment edges referencing removed QPX.adapted ids
let prunedEdges=0;
for(const f of readdirSync(COORD)){ if(!/^target-chain\..+\.json$/.test(f)||f==='target-chain.zz-qpilot.json') continue; const p=join(COORD,f); let x; try{ x=JSON.parse(readFileSync(p,'utf8')); }catch{ continue; } if(!Array.isArray(x.edges)) continue; const before=x.edges.length; x.edges=x.edges.filter(e=>!(String(e.from).includes('QPX.adapted')||String(e.to).includes('QPX.adapted'))); if(x.edges.length!==before){ writeFileSync(p, JSON.stringify(x,null,2)); prunedEdges+=before-x.edges.length; console.log('pruned edges in',f,before,x.edges.length); } }
console.log('cross-fragment pruned edges:',prunedEdges);
// drop *Adapted.lean from extra-targets
const etPath=join(ROOT,'dag','watchdog','extra-targets.txt'); const et=readFileSync(etPath,'utf8').split(/\r?\n/);
const lines=et.filter(Boolean); const keptEt=lines.filter(l=>!l.endsWith('Adapted.lean'));
writeFileSync(etPath, keptEt.join('\n')+'\n');
console.log('extra-targets:',lines.length,'->',keptEt.length,'removed',lines.length-keptEt.length);