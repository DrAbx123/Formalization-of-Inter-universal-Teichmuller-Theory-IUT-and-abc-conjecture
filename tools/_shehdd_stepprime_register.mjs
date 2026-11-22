import { readFileSync, writeFileSync } from 'node:fs';
const p='D:/lean/dag/target-chain.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const n=(j.nodes||[]).find(x=>x.id==='B4c-c-stepprovider');
if(!n){ console.log('node missing'); process.exit(0); }
const f='tmp/sheaf/xif/paper/Mzk1StepProviderPrimeActual.lean';
n.declarations = n.declarations || {};
n.declarations[f] = ['exists_maxDegP_finite','stepSetP1','mem_stepSetP1_of_mem','mem_stepSetP1_of_conj','mem_stepSetP1_of_crit','degQ_le_of_mem_conjSet','maxDegP_stepSetP1_le','F4NumMaxStrictInput','measure_stepSetP1_lt_of_named','StepProvider\'','StepProviderFixedBetaChoiceInput','F0StepTransportInput','stepProvider\'_of_inputs'];
n.note='A424 restated beta-f0; f1/f2/f4a PROVED in file; f4b (F4NumMaxStrictInput) + f5 (F0StepTransportInput) NAMED; assembly stepProvider\'_of_inputs PROVED conditional; fixed-beta equivalence named; repaired 4 compile errors (monic.ne_zero, membership defeq, calc <=, rows length 10) - watchdog recompile pending.';
writeFileSync(p, JSON.stringify(j,null,2));
console.log('updated node decls='+n.declarations[f].length);
