import { readFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const rel='tmp/sheaf/xif/paper/ShehddInd2LinkChainActual.lean';
const txt=readFileSync(ROOT+'/dag/watchdog/extra-targets.txt','utf8');
if(!txt.split('\n').includes(rel)){ appendFileSync(ROOT+'/dag/watchdog/extra-targets.txt', rel+'\n'); console.log('queued '+rel); } else console.log('already queued');
const doc=ROOT+'/coord/TMP-ASSET-MINE.md';
let dt=readFileSync(doc,'utf8');
const note='- 已消费: LeanFormal/IUT/IUTIII/Theorem311/Indeterminacy/Ind2Reduction.lean -> tmp/sheaf/xif/paper/ShehddInd2LinkChainActual.lean (shehdd:\u0020ind2-link-chain, 3 个真实链定理; A480)';
if(!dt.includes('ShehddInd2LinkChainActual')){ appendFileSync(doc, '\n'+note+'\n'); console.log('mine doc updated'); }
