import { readFileSync, writeFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/target-chain.shehdd.json';
const j=JSON.parse(readFileSync(p,'utf8'));
const file='tmp/sheaf/xif/paper/ShehddIUT312TopStatementActual.lean';
if(!j.nodes.some(n=>n.id==='iut312-top-statement')){
  j.nodes.push({
    id:'iut312-top-statement',
    kind:'target',
    title:'IUT III Cor 3.12 statement layer: qSigned <= thetaSigned (paper inequality mapping)',
    status:'CONDITIONAL',
    files:[file],
    declarations:{ [file]: ['IUT312TopStatement','iut312TopStatement_iff_cor312Conclusion','iut312TopStatement_of_contract','iut312TopStatement_chain'] },
    note:'PENDING-VERIFY (watchdog compile). Statement-level mapping of paper Cor 3.12 (-|log Theta| >= -|log q|) to Lean StepXIContract chain; contract => statement PROVED via tree cor312_of_constructed_stepXI. Paper objects (Theta-pilot/q-pilot/hull/Kummer/multiradial/Ind) remain NAMED elsewhere (iut-skeleton, e-deep, EtTh, AbsTopIII nodes).'
  });
  j.edges.push({from:'iut312-top-statement',to:'iutiii:IUTIII.COR312.TARGET',kind:'statement',evidence:'observed_source'});
  j.edges.push({from:'iut312-top-statement',to:'iut-pre-abc:Gap.iut312TopStatement',kind:'proof',evidence:'observed_source'});
}
writeFileSync(p, JSON.stringify(j,null,2));
const extra=ROOT+'/dag/watchdog/extra-targets.txt';
const cur=readFileSync(extra,'utf8');
if(!cur.includes(file)) appendFileSync(extra, file+'\n');
console.log('nodes='+j.nodes.length+' edges='+j.edges.length);
