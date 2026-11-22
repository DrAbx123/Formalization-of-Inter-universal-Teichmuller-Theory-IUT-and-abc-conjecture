import { readFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const prio=readFileSync(ROOT+'/dag/watchdog/priority-files.txt','utf8').split('\n').filter(Boolean);
const queue=readFileSync(ROOT+'/dag/watchdog/extra-targets.txt','utf8').split('\n').filter(Boolean);
const olean=f=>existsSync(ROOT+'/.lake/build/lib/lean/'+f.replace(/\.lean$/,'.olean'));
const groups={
 'R1/R2 tree assets':['LeanFormal/IUT/IUTIII/Theorem311/Output/MultiradialAlgorithmReduction.lean','LeanFormal/IUT/IUTIII/Theorem311/SourceFiniteMultiradial.lean','LeanFormal/IUT/IUTIII/Theorem311/Indeterminacy/Ind1Reduction.lean','LeanFormal/IUT/IUTIII/Theorem311/Indeterminacy/Ind2Reduction.lean','LeanFormal/IUT/IUTII/Kummer/K1K2BoundaryReduction.lean'],
 'literal axioms (others)':['tmp/sheaf/xif/paper/A482LiteralCarrierAxiomsActual.lean','tmp/sheaf/xif/paper/A483LiteralCarrierProductHaarActual.lean','tmp/sheaf/xif/paper/A482LiteralIQHullInterfaceActual.lean','tmp/sheaf/xif/paper/Mzk1LiteralIQHullFinitenessActual.lean','tmp/sheaf/xif/paper/Mzk1LiteralHullDetCompositionActual.lean','tmp/sheaf/xif/paper/Mzk1LiteralIQThirdTriangleActual.lean'],
 'R4 synthesis (others)':['tmp/sheaf/xif/paper/Mzk1FourTriangleSynthesisActual.lean'],
 'Example36 root':['LeanFormal/IUT/IUTII/Frobenioid/Example36LocalGaloisInvariantMonoid.lean','tmp/sheaf/xif/paper/Mzk1Example36CorrespondenceLawsActual.lean','tmp/sheaf/xif/paper/Mzk1Example36CorrespondenceLawsActualV2.lean'],
 'my green rung assemblies':['tmp/sheaf/xif/paper/ShehddFourTriangleAssemblyActual.lean','tmp/sheaf/xif/paper/ShehddIUT4CompareAssemblyActual.lean','tmp/sheaf/xif/paper/ShehddCVCompositionLawProvedActual.lean','tmp/sheaf/xif/paper/ShehddF4bStepProviderClosureActual.lean','tmp/sheaf/xif/paper/ShehddIndRouteCommuteChainActual.lean','tmp/sheaf/xif/paper/ShehddHeightVolumeChainActual.lean','tmp/sheaf/xif/paper/ShehddInd2LinkChainActual.lean','tmp/sheaf/xif/paper/ShehddFreyReductionChainActual.lean','tmp/sheaf/xif/paper/ShehddL02TateParameterChainActual.lean']
};
for(const [g,fs] of Object.entries(groups)){
  console.log('== '+g);
  for(const f of fs){ const src=existsSync(ROOT+'/'+f); console.log('  '+(olean(f)?'GREEN':'MISS ')+(src?' src':' NO-SRC ')+' | '+f+(queue.includes(f)?' [queued]':' [not-queued]')); }
}
console.log('PRIO count='+prio.length+' missing-olean='+prio.filter(f=>!olean(f)).length);
console.log('QUEUE count='+queue.length+' missing-olean='+queue.filter(f=>!olean(f)).length);
