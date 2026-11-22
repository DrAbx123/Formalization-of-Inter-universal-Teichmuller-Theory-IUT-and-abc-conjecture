import { readFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const idx=JSON.parse(readFileSync(ROOT+'/dag/generated/declarations-index.json','utf8')).declarations;
const names=new Set(idx.map(d=>d.name));
const items=[
 ['R4','LeanFormal/IUT/IUTIII/Corollary312/StepXI/APT.lean',['SourceAPTStatement','SourceAPTSlotAssembly','sourceAPTTransportSupply']],
 ['R4','LeanFormal/IUT/IUTIII/Corollary312/StepXI/ConcreteFiniteRouteColumns.lean',['finiteAPTData','finiteIPLSquare','finiteSHESquare']],
 ['R4','LeanFormal/IUT/IUTIII/Corollary312/StepXI/CertificateHullWiring.lean',['iqHullRealVolume','iqHullRealVolume_nonneg']],
 ['R4','LeanFormal/IUT/IUTIII/Corollary312/StepXI/CardQCMPComparison.lean',['QCMPComparisonSupply.toStepXIContract','cor312Conclusion_of_toStepXIContract']],
 ['R4','LeanFormal/IUT/IUTIII/Corollary312/StepXI/Contract.lean',['StepXIContract','Cor312Conclusion']],
 ['R4','LeanFormal/IUT/IUTIII/Corollary312/Comparison.lean',['cor312Conclusion_of_contract']],
 ['FF','LeanFormal/IUT/Foundations/AlgebraicGeometry/FiniteEtaleCoverFiber.lean',['geometricFiberFunctor','geometricFiberFunctor_map_id','geometricFiberFunctor_map_comp']],
 ['FF','LeanFormal/IUT/Foundations/Geometry/CurveEtaleFundamentalGroup.lean',['geometricFiberFunctor']],
 ['FF','LeanFormal/IUT/IUTII/Frobenioid/Example36CurveGaloisCategory.lean',['CurvePreGaloisCategoryRemainingFields']],
 ['FF','tmp/sheaf/xif/paper/S1794FiberFunctorProductActual.lean',['preservesTerminalObjectsField_holds','preservesPullbacksField_holds']],
 ['FF','tmp/sheaf/xif/paper/S2432PrestackCloseActual.lean',['test_slicePushNaturality']],
 ['QP','LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceThetaPilotScaledRegion.lean',['arithmeticTupleThetaPilotGenerator','arithmeticTupleThetaPilotRegion','arithmeticTupleThetaPilotExponent_nonneg','arithmeticTupleThetaPilotExactRadius']],
 ['QP','LeanFormal/IUT/IUTII/Kummer/SourceThetaPilotIQContainment.lean',['SourceThetaPilotOnePlacePacket','sourceThetaPilotProductMap','sourceThetaPilotTensorIQPacket','sourceThetaPilotIQPacket','possibleImage_subset_sourceThetaPilotIQPacket']],
 ['QP','LeanFormal/IUT/IUTIII/Corollary312/StepXI/CertificateHullWiring.lean',['thetaPilotCarrierFintype','sourceThetaPilotFiniteHull']],
 ['QP','LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/CardHullRealGeometryGapCards.lean',['possibleThetaPilotImageSet_eq_iUnion_singleton','possibleThetaPilotImageSet_eq_biUnion_finset']],
 ['QP','tmp/sheaf/xif/paper/S1929LiteralIQCarrierActual.lean',['rootExtensionProductThetaImage_oneThetaLabel']],
 ['QP','tmp/sheaf/xif/paper/GlobalIQHullThetaPilotActual.lean',['GlobalThetaPilotCarrier','globalThetaPilotImageSet','globalThetaPilotHull','globalThetaPilotImageSet_subset_hull']],
 ['I4','tmp/sheaf/xif/paper/S3131CanonicalRootedQCActual.lean',['S3131CanonicalRootedQC','S3131CanonicalRootedHC','S3131CanonicalRootedQC_le_HC']],
 ['I4','tmp/sheaf/xif/paper/S3131PaperRouteHeightReductionActual.lean',['heightUndilated']],
 ['I4','tmp/sheaf/xif/paper/S3131PaperRouteRegionReductionActual.lean',['regionUndilated']],
 ['I4','tmp/sheaf/xif/paper/S3131EndgameDependencyLedgerActual.lean',['S3131EndgameConditionalTheorem','endgame_conditional']],
 ['I4','Iut/Foundations/GaloisImage.lean',['imageComparison','imageComparison_inclusion','imageComparison_projection']]
];
for(const [g,f,ds] of items){
  const src=existsSync(ROOT+'/'+f);
  const ole=src&&existsSync(ROOT+'/.lake/build/lib/lean/'+f.replace(/\.lean$/,'.olean'));
  const bad=ds.filter(d=>!names.has(d)&&!names.has(d.split('.').pop()));
  console.log(g+' | '+f+' | src='+src+' olean='+ole+(bad.length?' | decl-not-found='+bad.join(','):''));
}
