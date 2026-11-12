# STEPXI-PRIOR-ART — inventory of HolomorphicHull prior assets

Status: READ-ONLY inventory, 2026-11-12. No compile.
Directory: LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/.
Files: 51 .lean (the request says 53; the extra 2 are not in this directory).
All 51 have current oleans under .lake/build/lib/lean/...; green here means
compiled, not that the paper carrier is constructed.

## 1. Summary

- 51 files, all olean-green.
- 24 files define an Audit Obligation; the rest are supporting finite/local/model
  layers without their own Obligation.
- Proven content: finite packet/determinant laws, hull-adjunction lattice laws,
  local-field product hull/module/volume laws, real-line Haar test carriers,
  and the final real arithmetic implication (Step (xi-f)):
  from -|log q| <= -|log Theta| and -|log Theta| <= CTheta*|log q|, conclude
  -1 <= CTheta.
- Reduction content: IQHullLogVolumeInterface, StepXIFiniteCertificate,
  Cor312ComparisonData, source q-side comparison, normalization/epsilon cards,
  and the Card-HULLREAL R9 chain. These reduce the target to explicit fields;
  the fields are not constructed for the actual source carrier.
- Missing final object: an actual StepXIFiniteCertificate / Cor312ComparisonData
  for the source, i.e. the field qPilot_mem_ray (-|log q| <= -|log Theta|) or
  the two fields q_le_hull and hull_le_theta with the scalar identifications.

## 2. Per-file inventory

Legend: Obligation = Audit obligation defined; key = main theorems; assumptions =
structures/certificates still needed; status: PROVED / MODEL / REDUCTION / GAP.

### 2.1 Finite packet, determinant, normalization core

| file | Obligation | key declarations | assumptions | status |
|---|---|---|---|---|
| Volume.lean | hullDeterminantLogVolume | PositivePacket, FiniteHull, StepXIFiniteCertificate; packetDet_eq_prod, packetLogVolume_eq_log_det, packetLogVolume_tensor, FiniteHull.average_le | finite packet positivity; no source hull | MODEL/PROVED |
| HullDeterminantLogVolumeReduction.lean | hullDeterminantLogVolumeReduction | HullDeterminantLogVolumeFrozenSpec; hullDeterminantLogVolumeFrozenSpec_holds; HolomorphicHullAdjunction; DetTensorPowerLogVolumeBookkeeping; Cor312ComparisonData; cor312CThetaLowerBound; Cor312ComparisonData.final_bound | adjunction fields; comparison data fields (qPilot_mem_ray, qParameter_log_ne_zero, qPilotLogVolume_eq) | PROVED finite+conditional |
| WeightedNormalization.lean | weightedDeterminantNormalization | WeightedDeterminantPacket; commonTensorDegree; normalizedLogVolume; weightedLogVolume_eq_commonTensorDegree_mul_normalizedLogVolume | packet denominators/positivity | PROVED |
| CertificateCThetaTransfer.lean | certificateCThetaTransfer | weighted_average_le_theta; cTheta_lower_bound_of_finiteCertificate; ..._expTwo | StepXIFiniteCertificate; hq:|log q|=-qSigned; hc:thetaSigned<=CTheta*|log q| | PROVED conditional |
| CertificateComparisonBridge.lean | certificateComparisonFaceBridge | StepXIFiniteCertificate.toCor312ComparisonData; Cor312ComparisonData.final_bound_of_certificate | certificate + scalar identifications | PROVED conditional |

### 2.2 Hull interface, normalization, q-side, source realization reductions

| file | Obligation | key declarations | assumptions | status |
|---|---|---|---|---|
| SourceHullCompactnessReduction.lean | iqHullLogVolume | IQHullLogVolumeInterface; imageSet_logVolume_le_hull; hull_logVolume_lt_top; lower_bound_and_finiteness | interface fields: imageSet/hull/monotone logVolume/unitRegion/scaleShift/hull_subset_scaleShift/finite unit/scale invariance | REDUCTION (interface) |
| SourceHullInterfaceDischarge.lean | iqHullInterfaceDischarge | hull_logVolume_realRepresentation; haarContractionInterface; sourceHullVolume_not_lt_top_of_degreeFaithful; sourceHullVolume_lt_top_of_compactnessInput; not_nonempty_valueHullCompactnessInput_of_degreeFaithful | ValueHullCompactnessInput or Haar contraction model; degree faithfulness obstructs | REDUCTION + obstruction |
| IQCarrierHaarData.lean | iqCarrierHaarData | SourceUnitRegionHaarData; image_mul_eq_scaledRegionImage; sourceSetVolume_le_ofReal_of_logDegree_le; sourceUnitRegionHaarInterface_hull_logVolume_lt_top | SourceUnitRegionHaarData | MODEL/REDUCTION |
| IQCarrierConcreteModel.lean | iqCarrierConcreteModel | real-line carrier model: logDegree, hull, imageSet, volume identities | real-line calibration only | MODEL |
| IQCarrierRealizationAlignment.lean | iqCarrierRealizationAlignment | iqCarrierAlignment_jointDictionaries_refuted; iqCarrierAlignment_specPackage_refuted; additive epsilon comparison | requires weight dictionary/volume card; refutes naive package | REDUCTION/negative results |
| IQHullValueCarrierWiring.lean | iqHullValueCarrierWiring | iqHullPointWiringCertificate; qSigned/thetaSigned/hullVolume; iqHullPointWiringCor312Conclusion; average_le | IQHullLogVolumeInterface W + point weighted values | REDUCTION |
| SourceValueHullRealizationBridge.lean | cardHullRealValueBridge | pointWeightedValues; ofReal_neg_one_le_imageVolume; hull_le_ofReal_toReal; sourceUnitRegionHaarPointWiringCertificate | source value realization + interface | REDUCTION |
| SourceHullNormalizationConditionalClosure.lean | cor312HullNormalizationConditionalClosure | Cor312SourceHullNormalizationData; ...EpsilonData; ...VertexCheckedData; ...LabelEpsilonCheckedData; *_hunit | vertex/label/epsilon checked data | REDUCTION |
| CardAMPLThetaBoundSupply.lean | cardAMPLThetaBoundSupply | CardAMPLThetaBoundSupply; realVolume_le; cor312Conclusion | interface-level theta upper supply | REDUCTION |
| HullVertexConvexityAssembly.lean | hullVertexConvexityAssembly | SourceHullConvexVertexData; sourceHullVolume_le_vertices; vertices_le_sourceHullVolume; eq_vertices | convex vertex data | REDUCTION |
| HunitEpsilonTransferReduction.lean | cor312HunitEpsilonTransfer | hunit_of_epsilon_hullBound; epsilon_hullBound_of_hunit; exists_epsilon iff exists degreeBound<=hullVolume | epsilon hull bound / degree bound | REDUCTION |
| OModuleCompactnessLayer.lean | cardHullRealOModuleCompactness | SourceOModuleLayer; SourceOneCircUCompactness; sourceOModuleCompactness_hullVolume_lt_top; pointWiring/normalizedQ conclusions | O-module compactness data | REDUCTION |
| SourceContractedSupplyRealization.lean | cardHullRealContractedSource | thetaValueAt_lt_one_of_q_lt_one; sourceHullVolume_lt_top_of_contractedGenerators; sourceContractedHullInterface | q<1 + contracted generators | REDUCTION (conditional) |
| SourceContractionWlogReduction.lean | cardHullRealContractionWlogReduction | neg_abs_log_le_of_wlog_negative_case; coefficient_ge_neg_one...; sourceContractedPilotWlogReduction; not_contractedGenerators_of_degreeFaithful | WLOG negative case / contracted generators | REDUCTION + obstruction |
| SourceArithmeticThetaPilotBridge.lean | - | ArithmeticThetaPilotBridge; sourceHullVolume_lt_top_of_arithmeticThetaPilotBridge; no_degreeFaithful...; not_nonempty... | arithmetic theta-pilot bridge data | REDUCTION |
| SourceUnitRegionHaarDataActual.lean | - | concrete nonpositive value model; sourceHaarActualDegree_nonpos; FPrimeStrip/Theater data | concrete nonpositive test carrier | MODEL |
| SourceImageHull.lean | - | ThetaPilotCarrier; ValueMonoidAt; thetaValueAt; logDegreeAt; SourceImageRealization; LiteralArithmeticHullInterface | value-monoid realization | MODEL/reduction base |
| SourceImageHullVolume.lean | sourceImageHullVolume | SourceVolumeIndex; sourceLocalLogDegree; sourcePointVolume; sourceHullVolume; degree-faithful formulas | degree faithfulness / logDegree recurrence | MODEL/REDUCTION |
| SourceQSideComparison.lean | - | iqHullCertificate_hqSlot_of_neg; sourceQSideNormalizedValue; sourceSetVolume_possibleImage_eq_iSup_sourceQSide; ..._ge_sourceQSide; ..._ofReal_of_sourceQSide_le; ..._eq_zero_of_forall_theta_lt_one | hdeg (logDegree identity); signed q comparison; theta<1 contraction | REDUCTION; q real gap |
| CardHullRealSignedLogVolume.lean | cardHullRealSignedLogVolume | sourceSignedHullLogVolume; sourceSignedImageLogVolume; *_nonpos; SourceXifSignedComparison; signed comparison iff | signed comparison data | REDUCTION |
| CardHullRealR9PointMembershipAudit.lean | cardHullRealR9PointMembershipAudit | downRay; mem_downRay_iff_le; sourceHullVolume_le_iff_pointwise_pointVolume_le; value vs witness forms | pointwise membership | AUDIT/REDUCTION |
| CardHullRealFinitePhaseGate.lean | cardHullRealFinitePhaseGate | toReal_top_collapse; sourceHullVolume_eq_top_of_exists_pos_logDegree; sourceHullVolume_le_imageVolume_iff_lt_top | degree faithfulness phase gate | AUDIT/obstruction |
| CardHullRealGeometryReduction.lean | cardHullRealGeometryReduction | sourceHolomorphicHull_eq_closure; sourceHullVolume_eq_imageVolume_iff; pointVolume comparisons | via-images identity R9/R10 | REDUCTION |
| CardHullRealGeometryGapCards.lean | cardHullRealGeometryGapCards | possibleThetaPilotImageSet finite/union; compact subset of lambda*O | topology/O-module gaps | GAP cards |
| CardHullRealEdgeNormalizationReduction.lean | cardHullRealEdgeNormalizationReduction | IQHullEdgeBoundInterface; productEdgeNormalization; sourceHullVolume_le_imageVolume_of_productEdgeNormalization | product-edge normalization | REDUCTION |
| CardHullRealEdgeNormalizationDichotomy.lean | cardHullRealEdgeNormalizationDichotomy | LogVolumeScaleDecomposition; multiplicativeNatScaleWitness; logScale_listProd_le_zero | multiplicative scaling dichotomy; edge bound | REDUCTION/negative |
| CardHullRealGeneratorNonpositivity.lean | cardHullRealGeneratorNonpositivity | logScale_eq_zero; LogVolumeScaleDecompositionNonempty; gaussExponent_one; nonpositive generator facts | generator nonpositivity | REDUCTION |
| CardHullRealHaarDilationDocking.lean | cardHullRealHaarDilationDocking | dilationContractionSubmonoid; logScale decomposition; half dilation logScale | real-line dilation docking | MODEL |

### 2.3 Local-field product hull, integral module, volume transport

| file | Obligation | key declarations | assumptions | status |
|---|---|---|---|---|
| LocalFieldProductHull.lean | - | unitRegion; region; exists_least_region; least_region_unique; hull; subset_hull | finite product local fields, proper spaces | PROVED local geometry |
| LocalFieldProductHullBlocks.lean | - | blockProjection; blockCoordinatesHomeomorph; mem_hull_iff_blocks_of_bound; image_hull_of_bound | boundedness for block decomposition | PROVED |
| LocalFieldProductHullTransport.lean | - | continuous_ringEquiv_image_region; image_hull_subset; image_hull | continuous ring equivalence | PROVED |
| LocalFieldProductLogVolumeTransport.lean | - | normalizedLogVolume_continuous_ringEquiv; hull version; addHaar version | Haar uniqueness/normalization | PROVED |
| LocalFieldProductUnitRegionMaps.lean | - | norm_le_one_of_compact_powers; continuous_ringHom_mem_unitRegion; image_unitRegion | compact powers | PROVED |
| LocalFieldIntegralHull.lean | - | integralRing; regionModule; exists_compact_integralModule_hull | nonarchimedean norm law | PROVED |
| LocalFieldIntegralHullSpan.lean | - | integralSpan_subset_hull; hull_subset_integralSpan; integralSpan_eq_hull | finite index | PROVED |
| LocalFieldIntegralTensorSpan.lean | - | rat_span_unitBall_eq_top; padic_rat_span_unitBall_eq_top; rat_span_integralTensors_eq_top | char zero, finite | PROVED |
| LocalFieldPacketNormalizedVolume.lean | - | padicPacketLogVolume; unitRegion; prime_smul; mul_prime; algEquiv | nonempty finite product; normalized Haar | PROVED |
| LocalFieldTensorDecomposition.lean | - | liftFactorAlgHoms; finiteTensor_formallyEtale; exists_finiteFieldProduct_tensor/piTensor | finite separable extensions, char zero | PROVED |

### 2.4 Real-line Haar test carrier

| file | Obligation | key declarations | assumptions | status |
|---|---|---|---|---|
| HaarTranslateInterface.lean | haarTranslateModel | HaarTranslateCarrier; measure_image_mul_translate; scaledUnitRegion; toIQHullLogVolumeInterface | locally compact group + Haar + scaling | MODEL |
| HaarTranslateRealLineInstance.lean | haarTranslateRealLineInstance | realLineHaarTranslateInterface; unitInterval; realLine_hull_measure_lt_top | Real Haar test carrier | MODEL witness |
| HaarTranslateRealLineConsumerWiring.lean | haarTranslateRealLineConsumerWiring | realLinePointWiringCertificate; qSigned/thetaSigned; Cor312Conclusion | real-line interface + Unit certificate | MODEL |
| HaarTranslateRealLineLogCompatibility.lean | haarTranslateRealLineLogCompatibility | realLine_volume_dilation; dilationLogWeight laws; normalizedRealLineVolume_dilation | Real-line dilation | MODEL |
| HaarTranslateRealLineLogFrobeniusCompatibility.lean | haarTranslateRealLineLogFrobeniusCompatibility | realLineLogHomotopy; logShellLogVolume_homotopy; Frobenius increments | Real-line log-shell model | MODEL |
| HaarTranslateRealLineProcessionAverage.lean | haarTranslateRealLineProcessionAverage | realLineProcessionAverage; add/smul/comp_equiv; logShellStep | finite label average | MODEL |
| HaarTranslateRealLineShellHomotopyRadialAngular.lean | haarTranslateRealLineShellHomotopyRadialAngular | RealLineLogShellHomotopySystem; compatibility; radial/angular components | Real-line shell homotopy | MODEL |
| PadicLogShellModel.lean | padicLogShellModel | padicLogShell_scaledUnitRegion_measure_eq; hull_measure_lt_top | Q_p additive/unit ball test carrier | MODEL |

All files in sections 2.1-2.4 have oleans; MODEL means a proved finite/real-line
calibration, not the paper carrier.

## 3. Already-proved final inequalities

1. cor312CThetaLowerBound (HullDeterminantLogVolumeReduction.lean)
   Input: qParameter != 0, -|log q| <= thetaLogVolume,
          thetaLogVolume <= CTheta*|log q|.
   Output: -1 <= CTheta.
   This is the terminal real arithmetic of Step (xi-f); it is fully proved, but
   the two hypotheses are the source comparison inputs.

2. Cor312ComparisonData.final_bound (same file)
   A Cor312ComparisonData contains thetaHullLogVolume, qPilotLogVolume,
   qPilot_mem_ray (qPilotLogVolume <= thetaHullLogVolume), qParameter>0,
   log q != 0, qPilotLogVolume = -|log q|.
   final_bound: if thetaHullLogVolume <= CTheta*|log q|, then -1 <= CTheta.
   The target -|log q| <= -|log Theta| is exactly the field qPilot_mem_ray;
   no constructor of this data for the actual source is present.

3. StepXIFiniteCertificate.weighted_average_le_theta and
   cTheta_lower_bound_of_finiteCertificate (CertificateCThetaTransfer.lean)
   Certificate fields: qSigned <= hullVolume <= thetaSigned, qSigned<0,
   and weighted hull average <= hullVolume.
   weighted_average_le_theta: weighted.average <= thetaSigned.
   cTheta_lower_bound_of_finiteCertificate: with hq:|log q|=-qSigned and
   hc:thetaSigned <= CTheta*|log q|, conclude -1<=CTheta.
   A one-point witness cTheta_lower_bound_of_finiteCertificate_expTwo is proved.

4. IQHullLogVolumeInterface.imageSet_logVolume_le_hull
   and hull_logVolume_lt_top (SourceHullCompactnessReduction.lean)
   Conditional on the interface (imageSet<=hull, monotone logVolume, finite
   unit region, hull inside scaleShift unit region, scale invariance).

5. SourceQSideComparison real q-side reduction
   sourceSetVolume_possibleImage_eq_iSup_sourceQSide;
   sourceSetVolume_possibleImage_ge_sourceQSide;
   sourceSetVolume_possibleImage_ge_ofReal_of_sourceQSide_le.
   These prove ENNReal/real image-volume lower bounds from a signed q value
   q <= sourceQSideNormalizedValue n j0, under hdeg.
   The ENNReal hq slot is degenerate for q<0 (iqHullCertificate_hqSlot_of_neg).

6. SourceHullNormalizationConditionalClosure:
   cor312SourceHullNormalizationData_hunit and vertex/label variants
   reduce hunit to explicit normalization data structures.

## 4. Green vs reduction vs obstruction

PROVED finite/local/model:
  Volume, HullDeterminantLogVolumeReduction (finite part), WeightedNormalization,
  all LocalField* files, all HaarTranslate* files, PadicLogShellModel,
  IQCarrierConcreteModel, SourceUnitRegionHaarDataActual (test model),
  CertificateCThetaTransfer (conditional transfer),
  HullVertexConvexityAssembly (conditional on vertex data).

REDUCTION to named residual assumptions:
  SourceHullCompactnessReduction (IQHullLogVolumeInterface),
  SourceHullInterfaceDischarge (ValueHullCompactnessInput or Haar contraction),
  SourceHullNormalizationConditionalClosure (normalization data),
  HunitEpsilonTransferReduction (epsilon/degree bound),
  CardAMPLThetaBoundSupply (theta upper supply),
  IQHullValueCarrierWiring/SourceValueHullRealizationBridge (interface + point values),
  SourceArithmeticThetaPilotBridge, SourceContractedSupplyRealization,
  SourceContractionWlogReduction, OModuleCompactnessLayer,
  CardHullReal* R9 chain, SourceQSideComparison (signed q data),
  CardHullRealSignedLogVolume (signed comparison data).

OBSTRUCTION / negative results (important not to try to bypass):
  - SourceHullInterfaceDischarge: under pointwise degree faithfulness the
    value-realized hull volume is top, so the interface finiteness field fails;
    ValueHullCompactnessInput is inconsistent with degree faithfulness.
  - CardHullRealFinitePhaseGate: toReal channels collapse top to zero and are
    not faithful; sourceHullVolume_eq_top of positive generator.
  - CardHullRealGeometryGapCards: missing topology/O-module/boundedness pieces.
  - IQCarrierRealizationAlignment: naive joint dictionary/spec package refuted.
  - SourceContractionWlogReduction: not_contractedGenerators_of_degreeFaithful.
  - SourceQSideComparison: under full theta contraction image volume is 0, so
    the ENNReal q-slot is only 0<=0.

## 5. Shortest gap chain from green assets to
   -|log q| <= -|log Theta|

The target is a real signed comparison. In the existing API it is exactly one of:
  (i) Cor312ComparisonData.qPilot_mem_ray, or
  (ii) StepXIFiniteCertificate.q_le_theta after identifying
       qSigned = -|log q| and thetaSigned = -|log Theta|.

Shortest honest chain:

  A. Construct the actual source q-side scalar:
     qPilotLogVolume = -|log q|.
     Current assets: SourceQSideComparison gives real q-side image-volume
     lower bounds from q <= sourceQSideNormalizedValue, but not the actual
     paper q realization. GAP: qPilotLogVolume_eq for the source.

  B. Construct the actual theta-hull scalar:
     thetaHullLogVolume = -|log Theta|.
     Current assets: IQHullLogVolumeInterface + SourceHullCompactnessReduction
     give finiteness and propagation if the interface is realized;
     SourceHullInterfaceDischarge shows value-level degree faithfulness makes
     hull volume top. GAP: actual carrier realization / normalization.

  C. Prove the comparison qPilotLogVolume <= thetaHullLogVolume:
     equivalently -|log q| <= -|log Theta|.
     Current assets:
       - SourceQSideComparison real q lower bound to image log-volume;
       - IQHullLogVolumeInterface.imageSet_logVolume_le_hull;
       - sourceHullVolume_le_ofReal_of_unitRegionHaarData / normalization
         data (SourceHullNormalizationConditionalClosure) for an upper envelope;
     but no theorem connects the actual q scalar to the hull scalar.
     GAP: this comparison itself; it is the field qPilot_mem_ray.

  D. If C is obtained, the terminal arithmetic is already green:
     cor312CThetaLowerBound / Cor312ComparisonData.final_bound gives
     -1 <= CTheta from the CTheta upper bound.

Equivalently, the shortest route through the certificate:
  1. construct StepXIFiniteCertificate for the actual source with
     qSigned=-|log q|, thetaSigned=-|log Theta|;
  2. its q_le_hull and hull_le_theta fields give qSigned<=thetaSigned;
  3. use CertificateCThetaTransfer for the terminal bound.
Step 1 is precisely the missing source-certificate construction; it is not
provided by any green file.

Minimal explicit GAPs:
  G1. actual q-side scalar / qPilot_log identification;
  G2. actual theta-hull normalization / hull log-volume identification;
  G3. hull-vs-image log-volume comparison, or the certificate fields
      q_le_hull and hull_le_theta;
  G4. optional CTheta upper bound thetaHull <= CTheta*|log q| (for the -1<=CTheta
      terminal form);
  G5. all scalar identifications |log q|=-qSigned and thetaSigned=-|log Theta|.

The green assets reduce the final arithmetic (G4/G5 conditional) but do not
close G1-G3. In particular, the target inequality is not proved for the paper
carrier; it is a field of Cor312ComparisonData / StepXIFiniteCertificate.

## 6. Reuse recommendation

- Reuse directly:
  cor312CThetaLowerBound, Cor312ComparisonData.final_bound,
  cTheta_lower_bound_of_finiteCertificate, weighted_average_le_theta,
  packet determinant/tensor/rescale laws, HolomorphicHullAdjunction lattice laws,
  LocalField* product hull/module/volume laws, HaarTranslate* real-line models,
  IQHullLogVolumeInterface monotonicity/finiteness lemmas.
- Use as reduction interfaces, not as proofs:
  SourceHullCompactnessReduction, SourceHullInterfaceDischarge,
  IQHullValueCarrierWiring, SourceValueHullRealizationBridge,
  SourceHullNormalizationConditionalClosure, HunitEpsilonTransferReduction,
  CardAMPLThetaBoundSupply, CardHullReal* R9 chain, SourceQSideComparison.
- Do not treat as realized:
  any one-point/Real-line/Q_p test carrier, any degree-faithful model,
  any source hull under degree faithfulness (volume top), and any q-slot
  argument that only uses ENNReal.ofReal with q<0.

No Lean file written; no compile claimed.