import { readFileSync, writeFileSync } from 'node:fs';
const p='D:/lean/coord/PROBE-AUDIT.md';
let txt=readFileSync(p,'utf8');
txt=txt.replace('mp/TauCetiPort/TauCeti/LinearAlgebra/Matrix/Alternating.lean','tmp/TauCetiPort/TauCeti/LinearAlgebra/Matrix/Alternating.lean');
txt=txt.replace('dag/watchdog/extra-targets.txt: 530 entries (290 non-probe + 240 auto probes)','dag/watchdog/extra-targets.txt: 557 entries after append-only refresh (non-probe + auto probes; dead entries for absent files removed)');
writeFileSync(p,txt);
console.log('fixed audit doc');
