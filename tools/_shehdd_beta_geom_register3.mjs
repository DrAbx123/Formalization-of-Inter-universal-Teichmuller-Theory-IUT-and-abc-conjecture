import { readFileSync, writeFileSync } from 'node:fs';
const p='D:/lean/coord/target-chain.routes.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const n=(j.nodes||[]).find(x=>x.id==='routes:problemC_nested_betaTrack');
const f='tmp/sheaf/xif/paper/Mzk1NestedInductionBetaTrackingGeometricActual.lean';
if(n && n.declarations && n.declarations[f]){
  const d=n.declarations[f];
  for(const x of ['paperScopeLemma24Statement_of_geometric_dischargedBase']) if(!d.includes(x)) d.push(x);
  n.note = n.note + ' BASE DISCHARGED: paperScopeLemma24Statement_of_geometric_dischargedBase uses baseCaseProvider_proved; only CV law + geometric step data remain hypotheses.';
  writeFileSync(p, JSON.stringify(j,null,2));
  console.log('decls='+d.length);
} else console.log('node/decl missing');
