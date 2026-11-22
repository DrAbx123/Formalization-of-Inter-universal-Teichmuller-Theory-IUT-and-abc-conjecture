#!/usr/bin/env node
// Simple queue helper: queue.txt is the only pending queue.
import { readFileSync, writeFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const OUT=ROOT+'/dag/watchdog';
const QUEUE=OUT+'/queue.txt';
const LOG=OUT+'/wq.log';
const norm=s=>s.trim().replaceAll('\\','/');
const readQ=()=>existsSync(QUEUE)?readFileSync(QUEUE,'utf8').split(/\r?\n/).map(norm).filter(Boolean):[];
const writeQ=xs=>{ const u=[...new Set(xs)]; writeFileSync(QUEUE,u.join('\n')+(u.length?'\n':'')); return u; };
const cmd=process.argv[2]||'status';
if(cmd==='add'){ const cur=readQ(); const add=process.argv.slice(3).map(norm); const n=writeQ([...cur,...add]); console.log(JSON.stringify({action:'add',added:add.length,queue:n.length})); }
else if(cmd==='remove'){ const cur=readQ(); const remove=new Set(process.argv.slice(3).map(norm)); const n=writeQ(cur.filter(x=>!remove.has(x))); console.log(JSON.stringify({action:'remove',removed:cur.length-n.length,queue:n.length})); }
else if(cmd==='clear'){ const n=writeQ([]); console.log(JSON.stringify({action:'clear',queue:n.length})); }
else { const q=readQ(); console.log(JSON.stringify({queue:q.length,files:q})); }
