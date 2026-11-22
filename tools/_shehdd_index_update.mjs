import { readFileSync, writeFileSync } from 'node:fs';
const p='D:/lean/coord/repo-route-index-data.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const targets=new Set([
 'LeanFormal/IUT/ABCBridge/Bridge/ABCGap2FiniteC3Supply.lean',
 'LeanFormal/IUT/IUTI/HodgeTheater/SourceDefinition31DualContractAlignment.lean',
 'LeanFormal/IUT/IUTIII/Theorem311/SourceK1K2CardReduction.lean'
]);
let changed=0;
for(const r of j.rows){ if(targets.has(r.file) && r.citable==='OLEAN_MISSING'){ r.citable='OLEAN_FRESH'; r.index_note='shehdd A460: olean present+fresh (evidence: results log EXIT0 for two IUT files; ABCGap2 import-shadowing fix compiled by watchdog/manual before A459, olean fresh)'; changed++; } }
if(j.stats && j.stats.citable){ j.stats.citable.OLEAN_MISSING = Math.max(0,(j.stats.citable.OLEAN_MISSING||0)-changed); j.stats.citable.OLEAN_FRESH = (j.stats.citable.OLEAN_FRESH||0)+changed; }
j.updated_by='shehdd A460 index fresh update';
writeFileSync(p, JSON.stringify(j,null,2));
console.log('changed rows='+changed+' OLEAN_MISSING='+j.stats.citable.OLEAN_MISSING+' OLEAN_FRESH='+j.stats.citable.OLEAN_FRESH);
