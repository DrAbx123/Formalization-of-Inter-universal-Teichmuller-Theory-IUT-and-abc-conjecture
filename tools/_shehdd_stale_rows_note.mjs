import { readFileSync, writeFileSync, existsSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/repo-route-index-data.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const note='A465 probe cleanup: probe-only row (decls=[]) whose probe file was removed in the one-off cleanup; not a CITABLE pin (no declarations/evidence cited). Kept as STALE_NO_SOURCE; rebuild on demand from node declarations. See coord/PROBE-AUDIT.md.';
const names=['tmp/sheaf/xif/paper/_FinalPaperXiFProbe.lean','tmp/sheaf/xif/paper/_PaperTargetProbe.lean','tmp/sheaf/xif/paper/_S1779RouteProbe.lean','tmp/sheaf/xif/paper/_s2857gaprobe.lean'];
let n=0;
for(const r of j.rows){ if(names.includes(r.file)){ r.index_note=note; n++; } }
// TauCeti row: locate actual path if exists
const tau='tmp/TauCetiPort/TauCeti/LinearAlgebra/Matrix/Alternating.lean';
const tauRow=j.rows.find(r=>r.file===tau);
if(tauRow){ tauRow.index_note='A465 index sync: path not present in current tree (pre-existing stale row, not caused by probe cleanup)'; }
writeFileSync(p, JSON.stringify(j,null,2));
console.log('notes updated='+n);
