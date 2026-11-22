import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const file='tmp/sheaf/xif/paper/ShehddInterfaceFormConsumerActual.lean';
if(!j.nodes.some(n=>n.id==='interface-form-consumer')){
  j.nodes.push({
    id:'interface-form-consumer',
    kind:'theorem',
    title:'Cor312ToABCBridgeInterface => ABC log form / additive form / height bound (consumer)',
    status:'CONDITIONAL',
    files:[file],
    declarations:{ [file]: ['abcLogConjecture_of_interface','abcHeightWeightAdditive_of_interface','interface_heightBound_and_additive','interfaceFormRows','interfaceFormRows_length'] },
    note:'PENDING-VERIFY (watchdog compile). Composes cor312ToABCBridge_abcConjecture/heightBound with the proved ABC log/additive equivalences; interface itself remains the named G2 input.'
  });
  j.edges.push({from:'interface-form-consumer',to:'T1-cor312-abc-bridge',kind:'proof',evidence:'observed_source'});
  j.edges.push({from:'interface-form-consumer',to:'mainline:abc-log-equivalence',kind:'statement',evidence:'observed_source'});
  j.edges.push({from:'interface-form-consumer',to:'mainline:abc-height-weight-additive',kind:'statement',evidence:'observed_source'});
}
writeFileSync(p, JSON.stringify(j,null,2));
const extra=ROOT+'/dag/watchdog/extra-targets.txt';
const cur=readFileSync(extra,'utf8');
if(!cur.includes(file)) appendFileSync(extra, file+'\n');
console.log('my nodes='+j.nodes.length+' edges='+j.edges.length);
