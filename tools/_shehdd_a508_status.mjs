import { readFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const q=readFileSync(ROOT+'/dag/watchdog/extra-targets.txt','utf8').split('\n').filter(Boolean);
const qs=new Set(q);
const cands=[
 'tmp/sheaf/xif/paper/Mzk1FourTriangleSharedActual.lean',
 'tmp/sheaf/xif/paper/Mzk1QPilotSHEDoubleImageActual.lean',
 'tmp/sheaf/xif/paper/Mzk1UnifiedObjectSkeletonActual.lean',
 'tmp/sheaf/xif/paper/Mzk1TakkunPrimeStripAdapterActual.lean',
 'tmp/sheaf/xif/paper/Mzk1Step3115ComparisonActual.lean',
 'tmp/sheaf/xif/paper/Mzk1QPilotR4Stage5AlignActual.lean',
 'tmp/sheaf/xif/paper/Mzk1R4LiteralAssemblyActual.lean',
 'tmp/sheaf/xif/paper/Mzk1R4EndgameCompositionActual.lean'
];
for(const f of cands){ const ole=existsSync(ROOT+'/.lake/build/lib/lean/'+f.replace(/\.lean$/,'.olean')); console.log(f+' queued='+qs.has(f)+' olean='+ole); }
console.log('queue total='+q.length);
