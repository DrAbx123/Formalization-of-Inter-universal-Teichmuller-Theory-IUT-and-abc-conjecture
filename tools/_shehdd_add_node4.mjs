import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const file='tmp/sheaf/xif/paper/ShehddGeomCoreRouteConsumerActual.lean';
if(!j.nodes.some(n=>n.id==='geomcore-route-consumer')){
  j.nodes.push({
    id:'geomcore-route-consumer',
    kind:'theorem',
    title:'finite-map route => precise GeometricCore witness AND old recast (combined consumer)',
    status:'CONDITIONAL',
    files:[file],
    declarations:{ [file]: ['route_precise_and_recast','geomCoreRouteConsumerRows','geomCoreRouteConsumerRows_length'] },
    note:'PENDING-VERIFY (watchdog compile). Composes Mzk1GeomCoreFiniteMapRouteActual.preciseWitness_of_route + recast_of_route; finite-map construction and line-bundle iso remain NAMED gaps (finiteMapRouteGapText). No new assumptions.'
  });
  j.edges.push({from:'geomcore-route-consumer',to:'foundation:D.gap.finiteMap',kind:'statement',evidence:'observed_source'});
  j.edges.push({from:'geomcore-route-consumer',to:'iut-pre-stage4:D.witness.precise',kind:'proof',evidence:'observed_source'});
}
writeFileSync(p, JSON.stringify(j,null,2));
const extra=ROOT+'/dag/watchdog/extra-targets.txt';
const cur=readFileSync(extra,'utf8');
if(!cur.includes(file)) appendFileSync(extra, file+'\n');
console.log('nodes='+j.nodes.length+' edges='+j.edges.length);
