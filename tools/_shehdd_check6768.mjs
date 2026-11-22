import { readFileSync } from 'node:fs';
const ROOT='D:/lean';
const j=JSON.parse(readFileSync(ROOT+'/coord/target-chain.shehdd.json','utf8'));
console.log('fragment nodes='+j.nodes.length+' edges='+j.edges.length);
console.log('has 67/68: '+j.nodes.filter(n=>n.id==='bad-support-chain'||n.id==='primitive-triple-chain').map(n=>n.id).join(','));
const extra=readFileSync(ROOT+'/dag/watchdog/extra-targets.txt','utf8');
console.log('extra has O: '+extra.includes('ShehddBadSupportChainActual')+', P: '+extra.includes('ShehddPrimitiveTripleChainActual'));
