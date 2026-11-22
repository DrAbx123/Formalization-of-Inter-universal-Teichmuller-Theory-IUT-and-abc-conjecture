import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const file='tmp/sheaf/xif/paper/ShehddHullFrozenSpecConsumerActual.lean';
if(!j.nodes.some(n=>n.id==='hull-frozen-spec-consumer')){
  j.nodes.push({
    id:'hull-frozen-spec-consumer',
    kind:'theorem',
    title:'frozen hull/det log-volume spec consumer API (tensor/rescale/hull-average projections)',
    status:'CONDITIONAL',
    files:[file],
    declarations:{ [file]: ['frozen_spec_log_tensor','frozen_spec_log_rescale','frozen_spec_hull_average','frozen_spec_holds','hullFrozenSpecRows','hullFrozenSpecRows_length'] },
    note:'PENDING-VERIFY (watchdog compile). Consumer projections of HullDeterminantLogVolumeFrozenSpec + its holds instance; reuses tree packet lemmas (Volume.lean) and hull average sandwich. No new assumptions.'
  });
  j.edges.push({from:'hull-frozen-spec-consumer',to:'iutiii:IUTIII.HULL.DET_LOG_VOLUME',kind:'statement',evidence:'observed_source'});
  j.edges.push({from:'hull-frozen-spec-consumer',to:'e-deep:E2.detScalingLaws',kind:'proof',evidence:'observed_source'});
}
writeFileSync(p, JSON.stringify(j,null,2));
const extra=ROOT+'/dag/watchdog/extra-targets.txt';
const cur=readFileSync(extra,'utf8');
if(!cur.includes(file)) appendFileSync(extra, file+'\n');
console.log('my nodes='+j.nodes.length+' edges='+j.edges.length);
