import { readFileSync, writeFileSync } from 'node:fs';
const p='D:/lean/coord/target-chain.iuti-ii.json';
const j=JSON.parse(readFileSync(p,'utf8'));
let n=0;
for(const node of j.nodes){
  if(node.id==='IUTII.Kummer.Absolute' && node.status==='GAP'){
    node.status='TREE_ASSET';
    node.note='BUILD GAP RESOLVED (shehdd, evidence-only): all 6 files have fresh oleans (AbsoluteKummerContinuity/Injection/Quotient, ConcreteEtaleKummerBridge, ContinuousKummerGerm, LocalUnitKummerInjectivity; runtime-status all_fresh=true). Asset tree available; no new math.';
    n++;
  }
}
if(n>0) writeFileSync(p, JSON.stringify(j,null,2));
console.log('updated='+n);
