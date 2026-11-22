import { readFileSync, writeFileSync, appendFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const file='tmp/sheaf/xif/paper/ShehddABCFrontierFormEquivalencesActual.lean';
if(!j.nodes.some(n=>n.id==='abc-frontier-form-equivalences')){
  j.nodes.push({
    id:'abc-frontier-form-equivalences',
    kind:'theorem',
    title:'ABCFrontier <=> ABC log form / additive height-weight form (composition consumer)',
    status:'CONDITIONAL',
    files:[file],
    declarations:{ [file]: ['abcLogConjecture_of_frontier','abcHeightWeightAdditive_of_frontier','abcFrontier_iff_abcLogConjecture','abcFrontier_iff_abcHeightWeightAdditive'] },
    note:'PENDING-VERIFY (watchdog compile). Composes existing PROVED equivalences: abcFrontier_iff_abcConjecture + abcConjecture_iff_abcLogConjecture + abcConjecture_iff_ABCHeightWeightAdditiveBoundV2. No new assumptions.'
  });
  j.edges.push({from:'abc-frontier-form-equivalences',to:'T3-abc-frontier',kind:'proof',evidence:'observed_source'});
  j.edges.push({from:'abc-frontier-form-equivalences',to:'mainline:abc-log-equivalence',kind:'proof',evidence:'observed_source'});
  j.edges.push({from:'abc-frontier-form-equivalences',to:'mainline:abc-height-weight-additive',kind:'proof',evidence:'observed_source'});
}
writeFileSync(p, JSON.stringify(j,null,2));
const extra=ROOT+'/dag/watchdog/extra-targets.txt';
const cur=readFileSync(extra,'utf8');
if(!cur.includes(file)) appendFileSync(extra, file+'\n');
console.log('fragment nodes='+j.nodes.length+' edges='+j.edges.length);
