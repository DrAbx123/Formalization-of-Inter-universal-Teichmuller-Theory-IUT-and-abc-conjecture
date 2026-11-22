import { readFileSync, writeFileSync } from 'node:fs';
const ROOT='D:/lean';
// 1) HeightVolume: drop the universe-sensitive frozenSpec theorem, keep solid chain
const hv=ROOT+'/tmp/sheaf/xif/paper/ShehddHeightVolumeChainActual.lean';
let t=readFileSync(hv,'utf8');
const marker='/-- **PROVED chain:** the frozen hull/det spec supplies';
if(t.includes(marker)){ const idx=t.indexOf(marker); t=t.slice(0,idx).trimEnd()+'\n\nend LeanFormal.IUT.XiFPaper.ShehddHeightVolumeChainActual\nend\n'; writeFileSync(hv,t); console.log('HeightVolume trimmed to solid theorem'); }
// re-touch fixed files so watchdog retries (src mtime must exceed failed_mtime)
const retry=['ShehddBadSupportChainActual','ShehddIntegralUnitsChainActual','ShehddSectionMapChainActual','ShehddPrimitiveTripleChainActual','ShehddQNormPowerChainActual','ShehddQCandidatePowChainActual','ShehddHeightVolumeChainActual','ShehddLocalLogInverseConsumerActual','ShehddIntegralUnitLogConsumerActual','ShehddQParameterConsumerActual'];
for(const n of retry){ const p=ROOT+'/tmp/sheaf/xif/paper/'+n+'.lean'; const c=readFileSync(p,'utf8'); writeFileSync(p,c); }
console.log('touched '+retry.length+' files for retry');
