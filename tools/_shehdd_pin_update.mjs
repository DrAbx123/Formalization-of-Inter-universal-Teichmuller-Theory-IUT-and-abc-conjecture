import { readFileSync, writeFileSync, statSync } from 'node:fs';
import { createHash } from 'node:crypto';
const p='D:/lean/coord/target-chain.routes.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const f='D:/lean/tmp/sheaf/xif/paper/Mzk1NestedInductionBaseDischargedActual.lean';
const buf=readFileSync(f); const sha=createHash('sha256').update(buf).digest('hex').slice(0,8).toUpperCase(); const size=buf.length;
const n=(j.nodes||[]).find(x=>x.id==='problemC_nested');
if(n){ n.note = n.note + ' CITABLE PIN: Mzk1NestedInductionBaseDischargedActual ' + size + 'B sha ' + sha + ' EXIT0 + probe EXIT0 (watchdog results log).'; writeFileSync(p, JSON.stringify(j,null,2)); console.log('pin ' + size + ' ' + sha); } else console.log('missing');
