import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const file='tmp/sheaf/xif/paper/ShehddQPilotLogVolumeSummaryActual.lean';
if(!j.nodes.some(n=>n.id==='qpilot-log-volume-summary')){
  j.nodes.push({
    id:'qpilot-log-volume-summary',
    kind:'theorem',
    title:'q-pilot normalized log-volume summary (Tate j comparison composition)',
    status:'CONDITIONAL',
    files:[file],
    declarations:{ [file]: ['qPilotLogVolume_summary','tateJInvariantLogVolume_summary','qPilot_norm_mul_j_norm_one','qPilotLogVolumeRows','qPilotLogVolumeRows_length'] },
    note:'PENDING-VERIFY (watchdog compile). Composes PROVED TateQPilotJComparison facts (positivity, log l.value, j=q-pilot log-volume, additive zero, multiplicative norm 1). General Theta-pilot/hull objects NAMED elsewhere.'
  });
  j.edges.push({from:'qpilot-log-volume-summary',to:'iut-pre-abc:QPilot',kind:'statement',evidence:'observed_source'});
  j.edges.push({from:'qpilot-log-volume-summary',to:'iut-skeleton:QPilot',kind:'proof',evidence:'observed_source'});
}
writeFileSync(p, JSON.stringify(j,null,2));
const extra=ROOT+'/dag/watchdog/extra-targets.txt';
const cur=readFileSync(extra,'utf8');
if(!cur.includes(file)) appendFileSync(extra, file+'\n');
console.log('nodes='+j.nodes.length+' edges='+j.edges.length);
