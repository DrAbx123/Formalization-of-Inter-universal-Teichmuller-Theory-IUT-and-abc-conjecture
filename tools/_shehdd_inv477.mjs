import { readFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const idx=JSON.parse(readFileSync(ROOT+'/dag/generated/declarations-index.json','utf8'));
const decls=idx.declarations;
const regions=[
 ['IUT III Cor 3.12 tree','LeanFormal/IUT/IUTIII/Corollary312/'],
 ['IUT III Thm 3.11 tree','LeanFormal/IUT/IUTIII/Theorem311/'],
 ['IUT II Kummer/log-shell','LeanFormal/IUT/IUTII/Kummer/'],
 ['IUT II other','LeanFormal/IUT/IUTII/'],
 ['IUT I (theta/hodge theater)','LeanFormal/IUT/IUTI/'],
 ['IUT IV','LeanFormal/IUT/IUTIV/'],
 ['ABC bridge/Frey/Tate','LeanFormal/IUT/ABCBridge/'],
 ['Foundations','LeanFormal/IUT/Foundations/'],
 ['paper layer tmp/sheaf','tmp/sheaf/xif/paper/'],
 ['external ported','tmp/external/ported/'],
 ['Mathlib package','.lake/packages/mathlib/'],
 ['paper corpus text','papers/motizuki_corpus/']
];
const stats=regions.map(([label,prefix])=>({label,prefix,files:new Set(),decls:0,kinds:{}}));
for(const d of decls){
  for(const s of stats){ if(d.file && d.file.startsWith(s.prefix)){ s.decls++; s.files.add(d.file); const k=d.kind||'?'; s.kinds[k]=(s.kinds[k]||0)+1; break; } }
}
for(const s of stats){ console.log(s.label+' | files='+s.files.size+' | decls='+s.decls+' | top='+Object.entries(s.kinds).sort((a,b)=>b[1]-a[1]).slice(0,4).map(x=>x[0]+':'+x[1]).join(',')); }
const keys=[
 ['StepXIContract','StepXIContract'],['Cor312Conclusion','Cor312Conclusion'],['Cor312Route','Cor312Route'],
 ['qPilotLogVolume','qPilotLogVolume'],['tateJInvariant','tateJInvariant'],
 ['IUT312 statement','IUT312|iut312'],
 ['SourceLogShellDatum','SourceLogShellDatum'],['integralLogShell','integralLogShell'],['unitLog','unitLog'],
 ['absoluteKummerMap','absoluteKummerMap'],['kummerRatioHom','kummerRatioHom'],['kummerMap','kummerMap'],
 ['ind1 quotient','ind1QuotientLift'],['PossibleImage closure','lowerClosure'],
 ['FrobeniusPictureGraphAut','FrobeniusPictureGraphAut'],
 ['HodgeTheater','HodgeTheater'],
 ['ABCFrontier','ABCFrontier'],['ABCHeightWeightAdditive','ABCHeightWeightAdditiveBoundV2'],
 ['FreyJProductHeightCriterion','ABCFreyJProductHeightCriterion'],
 ['StepXIFiniteCertificate','StepXIFiniteCertificate'],
 ['HullDetFrozenSpec','HullDeterminantLogVolumeFrozenSpec'],
 ['sourceHullVolume','sourceHullVolume'],
 ['abcOddBadPrimeSupport','abcOddBadPrimeSupport'],['freyAbcTateCandidateQ','freyAbcTateCandidateQ'],
 ['oddTheta','oddTheta'],['gaussExponent','gaussExponent'],['realThetaValue','realThetaValue'],
 ['tateParameterUnit','tateParameterUnit'],['CurveIndexedTateUniformization','CurveIndexedTateUniformization'],
 ['GeomCore precise witness','Mzk1GeometricCoreWitnessPrecise'],
 ['GenEll precise statement','GenEll15GeometricCoreStatementPrecise'],
 ['TauCeti abc','TauCeti'],
 ['abcConjecture_iff_tauCeti','abcConjecture_iff_tauCeti'],
 ['ind3 possible image','PossibleImage'],
 ['K1K2 boundary','k1BoundaryOf'],
 ['Ind3 closure','IsLowerClosed'],
 ['Kummer kernel','absoluteKummerMapQuotient']
];
for(const [label,reStr] of keys){
  const re=new RegExp(reStr);
  let n=0, ex=null;
  for(const d of decls){ if(re.test(d.name)){ n++; if(!ex && d.file) ex=d.name+' | '+d.file+':'+(d.line||''); } if(n>5000) break; }
  console.log('KEY '+label+' -> hits='+n+(ex?' | '+ex:' | NONE'));
}
// asset file existence + olean freshness
const assets=[
 'LeanFormal/IUT/IUTIII/Corollary312/StepXI/Contract.lean',
 'LeanFormal/IUT/IUTIII/Corollary312/Routes.lean',
 'LeanFormal/IUT/IUTIII/Corollary312/Comparison.lean',
 'LeanFormal/IUT/IUTIII/Corollary312/TateQPilotJComparison.lean',
 'LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/Volume.lean',
 'LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/HullDeterminantLogVolumeReduction.lean',
 'LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/CardHullRealGeometryReduction.lean',
 'LeanFormal/IUT/IUTIII/Theorem311/Indeterminacy/Ind1Reduction.lean',
 'LeanFormal/IUT/IUTIII/Theorem311/Indeterminacy/Ind3Reduction.lean',
 'LeanFormal/IUT/IUTIII/Theorem311/SourceK1K2CardReduction.lean',
 'LeanFormal/IUT/IUTIII/Theorem311/SourceLabelWeightedDiagonal.lean',
 'LeanFormal/IUT/IUTII/Kummer/SourceLogShellAbsTopIIIBridge.lean',
 'LeanFormal/IUT/IUTII/Kummer/SourceLocalLogShellDatum.lean',
 'LeanFormal/IUT/IUTII/Kummer/SourceLogShellCarrier.lean',
 'LeanFormal/IUT/IUTII/Kummer/KummerGaloisClass.lean',
 'LeanFormal/IUT/IUTII/Kummer/AbsoluteKummerInjection.lean',
 'LeanFormal/IUT/IUTII/Kummer/AbsoluteKummerQuotient.lean',
 'LeanFormal/IUT/IUTII/Kummer/AlgebraicClosureKummerRoots.lean',
 'LeanFormal/IUT/IUTII/Kummer/SourceThetaPilotIQContainment.lean',
 'LeanFormal/IUT/IUTI/HodgeTheater/SourceThetaLinkGraphAutomorphismReduction.lean',
 'LeanFormal/IUT/IUTI/HodgeTheater/SourceThetaLinkDisplacementReduction.lean',
 'LeanFormal/IUT/IUTI/HodgeTheater/SourceHodgeTheaterFamilyLawsReduction.lean',
 'LeanFormal/IUT/ABCBridge/Bridge/ABCFrontier.lean',
 'LeanFormal/IUT/ABCBridge/Bridge/Cor312ToABCBridgeInterface.lean',
 'LeanFormal/IUT/ABCBridge/Bridge/IUTToABC.lean',
 'LeanFormal/IUT/ABCBridge/Bridge/ABCEllipticHeightCriterion.lean',
 'LeanFormal/IUT/ABCBridge/Bridge/ABCFrontierSingletonReduction.lean',
 'LeanFormal/IUT/ABCBridge/Bridge/ABCFrontierHeightWeightRefutation.lean',
 'LeanFormal/IUT/ABCBridge/Arithmetic/ABCHeightArithmeticWeightComparison.lean',
 'LeanFormal/IUT/ABCBridge/Arithmetic/LogarithmicBoundEquivalence.lean',
 'LeanFormal/IUT/ABCBridge/Arithmetic/ABCInvariantCoprimality.lean',
 'LeanFormal/IUT/ABCBridge/Arithmetic/ABCInvariantRadicalBridge.lean',
 'LeanFormal/IUT/ABCBridge/Arithmetic/ABCNonemptyOddBadSupport.lean',
 'LeanFormal/IUT/ABCBridge/Geometry/FreyTateAnalyticInput.lean',
 'LeanFormal/IUT/ABCBridge/Geometry/FreyTateParameterComparison.lean',
 'LeanFormal/IUT/ABCBridge/Geometry/ABCModelHeightComparison.lean',
 'LeanFormal/IUT/ABCBridge/Geometry/FreyWeierstrassCurve.lean',
 'LeanFormal/IUT/Foundations/Geometry/TateCurveArithmetic.lean',
 'LeanFormal/IUT/Foundations/Geometry/TateCurvePadicEstimates.lean',
 'LeanFormal/IUT/Foundations/Geometry/TateJInvariantNorm.lean',
 'LeanFormal/IUT/Foundations/Geometry/TateUniformizationContract.lean',
 'LeanFormal/IUT/Foundations/Geometry/EllipticTorsion.lean',
 'LeanFormal/IUT/Foundations/LocalFields/LogarithmLocalInverse.lean',
 'LeanFormal/IUT/Foundations/LocalFields/IntegralUnitLogarithm.lean',
 'LeanFormal/IUT/Foundations/LocalFields/IntegralUnits.lean',
 'LeanFormal/IUT/Foundations/Theta/OddTheta.lean',
 'LeanFormal/IUT/Foundations/Theta/OddThetaShift.lean',
 'LeanFormal/IUT/Foundations/Theta/OddThetaNormalization.lean',
 'LeanFormal/IUT/Foundations/Theta/GaussianKernel.lean',
 'LeanFormal/IUT/Foundations/Theta/SignedLabelEquiv.lean',
 'LeanFormal/IUT/Foundations/NumberField/LocalQParameter.lean',
 'LeanFormal/IUT/Foundations/Arithmetic/Radical.lean',
 'LeanFormal/IUT/Foundations/Arithmetic/NormLog.lean',
 'LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Boundary.lean'
];
let have=0, haveNoSource=[], fresh=0, stale=[];
for(const f of assets){
  const src=ROOT+'/'+f;
  if(existsSync(src)){
    have++;
    const olean=ROOT+'/.lake/build/lib/lean/'+f.replace(/^LeanFormal\//,'LeanFormal/').replace(/\.lean$/,'.olean');
    if(existsSync(olean)){ fresh++; } else { stale.push(f); }
  } else haveNoSource.push(f);
}
console.log('ASSETS existing='+have+'/'+assets.length+' olean_fresh='+fresh+' missing_source='+haveNoSource.length+' stale_olean='+stale.length);
if(haveNoSource.length) console.log('MISSING SRC: '+haveNoSource.join(','));
if(stale.length) console.log('STALE: '+stale.join(','));
// paper-layer count and key paper files
const paperFiles=[...new Set(decls.filter(d=>d.file&&d.file.startsWith('tmp/sheaf/xif/paper/')).map(d=>d.file))];
console.log('PAPER files='+paperFiles.length);
console.log('EXAMPLES: '+paperFiles.slice(0,10).join(' ; '));
// searches for missing verbatim names
const missingTests=[
 ['Cor 4.10 verbatim name',/cor4[._]?10|corollary4[._]?10/i],
 ['Def 3.8(i) theta-pilot object layer name',/thetaPilotSpecificObject|ThetaPilotDef38|thetaPilotObjectLayer/i],
 ['Def 3.1(b) standalone q-parameter object',/qParameterDef31|QParameterDef|def31b/i],
 ['H6 geometric core precise',/geometricCorePrecise|H6Precise/i],
 ['Sources 1995-2015 external named',/sources1995|S1995/i]
];
for(const [label,re] of missingTests){
  let n=0; const ex=[];
  for(const d of decls){ if(d.file&&re.test(d.file)){ n++; if(ex.length<2) ex.push(d.name+'@'+d.file); } }
  console.log('MISSINGTEST '+label+' file-hits='+n+(n?' e.g. '+ex.join(' ; '):' NONE'));
}
