import { readFileSync, writeFileSync } from 'node:fs';
const p='D:/lean/coord/target-chain.routes.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const n=(j.nodes||[]).find(x=>x.id==='routes:problemC_nested_betaTrack');
if(n){ n.note = n.note + ' FIX: beta file needed open Mzk1P1MorphismInterfaceActual (P1Point unknown); geometric file same; both touched, watchdog recompile pending.'; writeFileSync(p, JSON.stringify(j,null,2)); console.log('note updated'); } else console.log('missing');
