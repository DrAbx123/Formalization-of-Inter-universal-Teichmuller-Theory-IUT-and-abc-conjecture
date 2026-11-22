import { readFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const idx=JSON.parse(readFileSync(ROOT+'/dag/generated/declarations-index.json','utf8')).declarations;
const byFile={}; for(const d of idx){ if(d.file){ (byFile[d.file]=byFile[d.file]||[]).push(d.name); } }
const files=[
 'tmp/sheaf/xif/paper/S1929LiteralIQCarrierActual.lean',
 'tmp/sheaf/xif/paper/PaperIQCarrierActual.lean',
 'tmp/sheaf/xif/paper/IQCarrierFromSource.lean',
 'tmp/sheaf/xif/paper/GlobalIQHullInterfaceActual.lean',
 'tmp/sheaf/xif/paper/GlobalIQHullThetaPilotActual.lean',
 'tmp/sheaf/xif/paper/S2723GlobalIQHullActual.lean',
 'tmp/sheaf/xif/paper/S2958HalfIQHullCertificateActual.lean',
 'tmp/sheaf/xif/paper/S3129IQHullLogVolumeSourceActual.lean',
 'tmp/sheaf/xif/paper/IQCarrierHaarDataActual.lean',
 'LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/IQCarrierConcreteModel.lean',
 'LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/IQCarrierHaarData.lean',
 'LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/IQHullValueCarrierWiring.lean',
 'LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceUnitRegionHaarDataActual.lean',
 'LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceHullInterfaceDischarge.lean',
 'LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceHullCompactnessReduction.lean',
 'LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/CardHullRealGeometryReduction.lean',
 'LeanFormal/IUT/IUTII/Kummer/SourceLogShellIQTensorPacket.lean',
 'LeanFormal/IUT/IUTII/Kummer/SourceLogShellCarrier.lean',
 'LeanFormal/IUT/IUTII/Kummer/SourceLocalLogShellDatum.lean',
 'LeanFormal/IUT/IUTIII/Theorem311/SourceThetaPilotIQContainment.lean',
 'LeanFormal/IUT/IUTIII/Theorem311/SourceFiniteMultiradial.lean',
 'LeanFormal/IUT/Foundations/Geometry/ClosedBallInstanceFromProperSpace.lean',
 'LeanFormal/IUT/Foundations/Geometry/CompletionProperSpaceConsumer.lean',
 'LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceIQHullLogShellRegion.lean',
 'LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceIQHullSignedCertificateNonvacuous.lean',
 'LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceIQHullInterface.lean',
 'LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceIQHullSharpUpperBound.lean'
];
for(const f of files){
  const exists=existsSync(ROOT+'/'+f);
  const olean=existsSync(ROOT+'/.lake/build/lib/lean/'+f.replace(/\.lean$/,'.olean'));
  const ds=(byFile[f]||[]);
  console.log('FILE '+f+' | src='+exists+' olean='+olean+' decls='+ds.length);
  console.log('  '+(ds.slice(0,8).join(', ')||'(none in index)'));
}
