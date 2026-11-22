import tmp.sheaf.xif.paper.S3131FinalResidualRegistryActual
import tmp.sheaf.xif.paper.S3131RegistryGateOwnersActual
import tmp.sheaf.xif.paper.S3131RegistryLengthActual
import tmp.sheaf.xif.paper.S3131RegistryABCStrengthActual
import tmp.sheaf.xif.paper.S3131RegistryProbeActual
import tmp.sheaf.xif.paper.S3135FinalAssemblyGateActual
import tmp.sheaf.xif.paper.S3131CanonicalRootedQCActual
import tmp.sheaf.xif.paper.S3134FourthTriangleCompositionStatusActual
import tmp.sheaf.xif.paper.S3134MainlineRootedHFaActual
import tmp.sheaf.xif.paper.S3134LastSeamExactMissingActual
import tmp.sheaf.xif.paper.S3134CuspUniformizerActual
import tmp.sheaf.xif.paper.S3140ThetaNormalizationLegActual
import tmp.sheaf.xif.paper.S3140NormalizedRootResidualActual
import tmp.sheaf.xif.paper.S3132ThetaNormalizationFactorActual
import tmp.sheaf.xif.paper.S3132CanonicalRootedThetaTargetActual
import tmp.sheaf.xif.paper.S3132ThetaHalfResidualRegistryActual
import tmp.sheaf.xif.paper.S3132CanonicalVFormValueActual
import tmp.sheaf.xif.paper.S3132ThetaHalfDependencyChainActual
import tmp.sheaf.xif.paper.S3132GateThetaHalfConsumptionActual
import tmp.sheaf.xif.paper.S3132SharperThetaTargetReductionActual
import tmp.sheaf.xif.paper.S3132QThetaConsumerWiringActual
import tmp.sheaf.xif.paper.S3137SameCModelMapResidualActual
import tmp.sheaf.xif.paper.S3137QThetaComparisonBridgeActual
import tmp.sheaf.xif.paper.S3137NativeToC3SameCReadoutActual
import tmp.sheaf.xif.paper.S3137QThetaComparisonSummaryActual
import tmp.sheaf.xif.paper.S3137GaussianR1ResidualLightActual
import tmp.sheaf.xif.paper.S3137C3TensorBlockDimensionActual
import tmp.sheaf.xif.paper.S3137R1RegistryCanonicalActual
import tmp.sheaf.xif.paper.S3137R1ThetaHalfConsumerActual
import tmp.sheaf.xif.paper.S3137R1FinalStateActual
import tmp.sheaf.xif.paper.S3135F5ActualReductionActual
import tmp.sheaf.xif.paper.S3135TightnessActual
import tmp.sheaf.xif.paper.S3135EndToEndV2Actual
import tmp.sheaf.xif.paper.S3135FinalAssemblyGateV3Actual
import tmp.sheaf.xif.paper.S3135HaarModulusActual
import tmp.sheaf.xif.paper.S3135ValueGroupDegreeActualActual
import tmp.sheaf.xif.paper.S3136LGPJvPacketTransportActual
import tmp.sheaf.xif.paper.S3136LGPRealifiedValueTransportActual
import tmp.sheaf.xif.paper.S3136LGPLocalTensorPacketActual
import tmp.sheaf.xif.paper.S3139FirstTriangleMutationActual
import tmp.sheaf.xif.paper.S3139FirstTriangleFieldBActual

/-!
# S3140 PROJECT-LEVEL CLOSURE / AUDIT GATE

**task-46.**  Single audit-gate artifact importing the current key citable
stream files (verified present, fresh olean, EXIT=0 before import):

* final assembly gate: `S3135FinalAssemblyGateActual` (transitively F4 hull
  residual, F4 log-shell degree, scaling normalization, log-shell value group,
  F4 value-group degree/identification, F5 reduction, EndToEnd V2, Tightness);
* mainline canonical Q_C: `S3131CanonicalRootedQCActual`;
* shehdd fourth triangle: `S3134FourthTriangleCompositionStatusActual`,
  `S3134MainlineRootedHFaActual` (canonical Q_C consumption + signed 3.11.5=>3.12
  leg), `S3134LastSeamExactMissingActual` (last-seam field-level exact missing),
  `S3134CuspUniformizerActual` (constructed real cusp parameter + same-C
  epsilon residual);
* hull C3/Theta consumer: `S3132QThetaConsumerWiringActual`, and the
  hull task-41 normalization components `S3132ThetaNormalizationFactorActual`
  (raw Haar -> degree-normalized V-form channel, exact normalization factor) and
  `S3132CanonicalRootedThetaTargetActual` (canonical rooted Theta target
  `thetaPilotHullLogVolumeReal C3 = S3131CanonicalRootedHC T mu` structure);
* task-50 canonical/Theta-leg components: `S3140ThetaNormalizationLegActual`
  (raw last-seam Theta equality rewritten in hull's `c3ThetaRawHaarLogVolume`
  naming; hull normalization channel => canonical rooted Theta target => task-30
  Theta half => fourth-triangle Step (xi-f) ray) and
  `S3140NormalizedRootResidualActual` (mainline task-48/49 reduced
  `S3140NormalizedTwoLthRootSupply` for the explicit numeric Q_C formula; no
  numeric equality claimed);
* V3 final assembly gate + Haar modulus: `S3135FinalAssemblyGateV3Actual`,
  `S3135HaarModulusActual` (F4 (b) additive-Haar modulus law component);
* lattice R1 M-list: `S3137SameCModelMapResidualActual`;
* F5 cards: `S3135F5ActualReductionActual`, `S3135TightnessActual`;
* end-to-end chain: `S3135EndToEndV2Actual`, `S3135ValueGroupDegreeActualActual`;
* LGP components: `S3136LGPJvPacketTransportActual`,
  `S3136LGPRealifiedValueTransportActual`, `S3136LGPLocalTensorPacketActual`;
* first triangle: `S3139FirstTriangleMutationActual`,
  `S3139FirstTriangleFieldBActual`;
* lattice canonical residual index data artifacts (`S3137CanonicalResidualIndexActual`
  Part1/2/3/4 + maintenance + report) are cited as data-only references but kept
  OUT of this gate's imports so the acceptance dependency closure stays fully
  fresh and churn-free; only the R1 canonical overlay files below are imported.
* mainline FINAL RESIDUAL REGISTRY (task-49 handoff):
  `S3131FinalResidualRegistryActual` (15 registry entries with owner/page
  refs/ABC-strength flag/dependency order; hull ThetaHalf split into
  `ThetaHalf.vform-canonical-residual` + `ThetaHalf.exact-factor-residual`), `S3131RegistryGateOwnersActual`
  (14 id -> owner pairs + length check), `S3131RegistryLengthActual`
  (length = 14), `S3131RegistryABCStrengthActual` (only
  `F4.c.cardP-ABC-strength` is ABC-strength), `S3131RegistryProbeActual`.
  Checks below: registry length, owner-dictionary length, ABC-strength list,
  owner coverage of all registry ids, and no dangling dependsOn ids.

## Status (project level)

Proved / consumed unconditionally by the gate chain: F5 card U, F4 log-shell
degree construction, realified degree section, mainline paper-faithful
Q_C <= H_C (unconditional signed), shehdd's four-triangle composition and
canonical Q_C signed wiring, hull's C3/Theta consumer reductions.

Remaining named residuals (each with owner and construction plan in the
respective ledger entries; these are inputs of the final conditional theorem,
not errors):
1. `S3135PointLogShellFaithfulness` (F4 (a), owner abc; reduced to
   `S3135ValueMonoidIdentification`);
2. `S3135ScalingLogDegreeZero` (F4 (b) additive-Haar modulus law, owner abc);
3. `S3135ActualPointWeightCard` at the constructed point (F5 card P; exactly
   ABC-strength by `s3135_pointWeightCard_iff_abcConjecture`).
4. Theta-side C3-packet readout identification (hull task-38/41; consumer
   `S3132QThetaConsumerWiringActual` / last-seam Theta half) — independent of
   the F4/F5 => ABC implication, needed for the Cor 3.12 side of the fourth
   triangle.
5. Same-C source identifications: R1 M0 native T <-> OriginalInput
   (`S3137SameCModelMapResidualActual.SameCModelMapResidual`) and shehdd's
   `S3134SameCContractBridgeEpsilonResidual` (blocked on M0); mainline S778
   explicit-numeric Q_C gap (not claimed).  Mainline task-48 reduced that gap to
   ONE exact missing actual object: `Nonempty (ArithmeticTuplePureFractionalScalingData
   (qVFamTensorPlaces T b) qVFamTensorTuple (rootHalfCoefficient T b))` -- the
   actual 2l-th root generator in the NORMALIZED (Q_p-spectral) completion at
   `rootHalfCoefficient = c_norm/(2l)` (the tree's TwoLthRootKumaActual gives the
   root only in the default residue-norm completion; normalized passage is the
   same e-normalization as R1 M2 / R2).  With that supply the formula is a
   theorem by the proved Haar computation; until then `S3134CanonicalQFormulaGap`
   stays the named residual and NO numeric equality is claimed.
6. LGP local packet / Jv transport / realified transport residual structures
   (`LGPJvPacketTransportMissing`, `LGPRealifiedValueTransportGap`,
   `LGPLocalPacketIdentificationGap`); first-triangle FieldB contract data.

The gate theorem below is the single conditional entry point:
three final-gate residuals => `ABCConjecture`, with the F5 slot tight.
No sorry/axiom/arbitrary carrier is introduced here; all `#print axioms` below
are expected to be exactly `[propext, Classical.choice, Quot.sound]`.

## Static consistency scan of the import closure (task-46)

432 project files in the gate's import closure, 0 missing import paths.  Token
scan: 172 occurrences of the word "sorry", 171 of them prose in module docs
("No sorry/axiom/..." statements); scan for code-like sorry/admit finds ONE REAL
CODE TOKEN: `tmp/sheaf/n8/closure/NativeC3.lean:185`,
`nativeTensorLandingDonor_nonempty ... := by sorry` (contradicting that file's own
"zero-sorry" header).  It has NO consumers in the tree and no gate-chain
`#print axioms` output contains `sorryAx` (all trio), so it does not taint this
closure; it is recorded as an open audit finding: owner = Lead-assigned
n8-closure owner (file is outside qpilot/hull/shehdd prefixes; qpilot confirmed
not theirs), action = delete the unused theorem or restate it as an explicit
exact-Missing Prop with the donor construction plan.  No axiom/opaque/unsafe
declarations were found in the closure.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

open LeanFormal.IUT
open LeanFormal.IUT.Audit
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3135F4ActualHullResidualActual
open LeanFormal.IUT.XiFPaper.S3135ActualF4LogShellDegreeActual
open LeanFormal.IUT.XiFPaper.S3135ScalingNormalizationActual
open LeanFormal.IUT.XiFPaper.S3135LogShellValueGroupActual
open LeanFormal.IUT.XiFPaper.S3135F5ActualReductionActual
open LeanFormal.IUT.XiFPaper.S3135EndToEndV2Actual
open LeanFormal.IUT.XiFPaper.S3135TightnessActual
open LeanFormal.IUT.XiFPaper.S3135FinalResidualActual
open LeanFormal.IUT.XiFPaper.S3135ResidualNarrowingActual
open LeanFormal.IUT.XiFPaper.S3135ValueGroupDegreeActualActual
open LeanFormal.IUT.XiFPaper.S3135ValueGroupIdentificationActual
open LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateActual

namespace LeanFormal.IUT.XiFPaper.S3140ClosureGateActual

/-- **Project-level closure gate (single conditional entry point).**  From the
three final-gate residuals (F4 (a) point log-shell faithfulness, F4 (b) scaling
log-degree zero, F5 card P at the constructed point) the full chain yields
`ABCConjecture`. -/
theorem s3140_projectClosureGate
    {l₀ : PrimeGeFive} {V₀ : Type} (I₀ : OriginalInput l₀ V₀) (v₀ : V₀)
    (R₀ : I₀.SourceImageRealization v₀) (n₀ : ThetaPilotCarrier l₀)
    (D₀ : I₀.SourceUnitRegionHaarData v₀ R₀ n₀)
    (hpt : S3135PointLogShellFaithfulness I₀ v₀ R₀)
    (hzero : S3135ScalingLogDegreeZero I₀ v₀ R₀ n₀ D₀)
    (hP : S3135ActualPointWeightCard I₀ v₀ R₀ n₀ D₀ (abcSourcePoint I₀ v₀ R₀)) :
    ABCConjecture :=
  s3135_finalAssemblyGate I₀ v₀ R₀ n₀ D₀ hpt hzero hP

/-- Tightness of the project-level gate: under the two F4 cards, F5 card P is
equivalent to `ABCConjecture`, so the residual set cannot be weakened in the F5
slot. -/
theorem s3140_projectClosureGate_tight
    {l₀ : PrimeGeFive} {V₀ : Type} (I₀ : OriginalInput l₀ V₀) (v₀ : V₀)
    (R₀ : I₀.SourceImageRealization v₀) (n₀ : ThetaPilotCarrier l₀)
    (D₀ : I₀.SourceUnitRegionHaarData v₀ R₀ n₀)
    (hpt : S3135PointLogShellFaithfulness I₀ v₀ R₀)
    (hzero : S3135ScalingLogDegreeZero I₀ v₀ R₀ n₀ D₀) :
    S3135ActualPointWeightCard I₀ v₀ R₀ n₀ D₀ (abcSourcePoint I₀ v₀ R₀) ↔
      ABCConjecture :=
  s3135_finalAssemblyGate_tight I₀ v₀ R₀ n₀ D₀ hpt hzero

end LeanFormal.IUT.XiFPaper.S3140ClosureGateActual

/-! ## Axiom gate: final theorem and key intermediates -/

#print axioms LeanFormal.IUT.XiFPaper.S3140ClosureGateActual.s3140_projectClosureGate
#print axioms LeanFormal.IUT.XiFPaper.S3140ClosureGateActual.s3140_projectClosureGate_tight
#print axioms LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateActual.s3135_finalAssemblyGate
#print axioms LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateActual.s3135_finalAssemblyGate_tight
#print axioms LeanFormal.IUT.XiFPaper.S3131CanonicalRootedQCActual.S3131CanonicalRootedQC_le_HC
#print axioms LeanFormal.IUT.XiFPaper.S3131CanonicalRootedQCActual.S3131CanonicalRootedMagnitude
#print axioms LeanFormal.IUT.XiFPaper.S3134MainlineRootedHFaActual.S3134CanonicalRootedQC_le_HC
#print axioms LeanFormal.IUT.XiFPaper.S3134MainlineRootedHFaActual.S3134Step3115_canonicalQC_le_thetaPilot
#print axioms LeanFormal.IUT.XiFPaper.S3134MainlineRootedHFaActual.S3134Step3115_mainlineQC_le_thetaPilot_viaMainlineRooted
#print axioms LeanFormal.IUT.XiFPaper.S3134CuspUniformizerActual.S3134Step3115_mainlineQC_le_thetaPilot_viaEpsilon
#print axioms LeanFormal.IUT.XiFPaper.S3134CuspUniformizerActual.S3134SameCContractBridge_ofEpsilonResidual
#print axioms LeanFormal.IUT.XiFPaper.S3134LastSeamExactMissingActual.S3134FourthTriangleToC3ReadoutIdentification_iff_exactMissing
#print axioms LeanFormal.IUT.XiFPaper.S3134LastSeamExactMissingActual.S3134FourthTriangleResidual_of_exactMissing
#print axioms LeanFormal.IUT.XiFPaper.S3134FourthTriangleCompositionStatusActual.S3134FourthTriangle_hullDet_after_SHE
#print axioms LeanFormal.IUT.XiFPaper.S3134FourthTriangleCompositionStatusActual.S3134FourthTriangleResidual_of_R1Identification
#print axioms LeanFormal.IUT.XiFPaper.S3132QThetaConsumerWiringActual.S3134QThetaComparisonGap_of_c3HullReadout
#print axioms LeanFormal.IUT.XiFPaper.S3132QThetaConsumerWiringActual.S3134QThetaComparison_final_of_c3HullReadout
#print axioms LeanFormal.IUT.XiFPaper.S3137SameCModelMapResidualActual.qThetaPilotLogVolumeComparison_of_modelMap
#print axioms LeanFormal.IUT.XiFPaper.S3137SameCModelMapResidualActual.nativeToC3Identification_of_modelMap
#print axioms LeanFormal.IUT.XiFPaper.S3135TightnessActual.s3135_abcConjecture_of_threeResiduals
#print axioms LeanFormal.IUT.XiFPaper.S3135TightnessActual.s3135_pointWeightCard_iff_abcConjecture
#print axioms LeanFormal.IUT.XiFPaper.S3135EndToEndV2Actual.s3135_abcConjecture_of_endToEndInputsV2
#print axioms LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateV3Actual.s3135_finalAssemblyGateV3
#print axioms LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateV3Actual.s3135_finalAssemblyGateV3_tight
#print axioms LeanFormal.IUT.XiFPaper.S3132CanonicalRootedThetaTargetActual.S3134Step3115ThetaPilotReadout_eq_thetaPilot_of_canonical
#print axioms LeanFormal.IUT.XiFPaper.S3132ThetaNormalizationFactorActual.thetaPilotHullLogVolumeReal_eq_canonical_of_factor_zero
#print axioms LeanFormal.IUT.XiFPaper.S3132ThetaNormalizationFactorActual.thetaNormalizationFactor_eq
#print axioms LeanFormal.IUT.XiFPaper.S3135HaarModulusActual.s3135_haar_unit_scaling
#print axioms LeanFormal.IUT.XiFPaper.S3135ValueGroupDegreeActualActual.s3135_realifiedDegreeSection
#print axioms LeanFormal.IUT.XiFPaper.S3136LGPJvPacketTransportActual.lgpRoot_mem_thetaValueSubgroup
#print axioms LeanFormal.IUT.XiFPaper.S3136LGPRealifiedValueTransportActual.lgpRealifiedValueTransport_compat
#print axioms LeanFormal.IUT.XiFPaper.S3136LGPLocalTensorPacketActual.lgpBadLocalPacket_place_agree
#print axioms LeanFormal.IUT.XiFPaper.S3139FirstTriangleMutationActual.sourceMultiradialMutationOfBPS_point_invariant
#print axioms LeanFormal.IUT.XiFPaper.S3139FirstTriangleFieldBActual.sourceFirstTriangleMutationData_gluing_invariant
#print axioms S3131FinalResidualRegistry_length
#print axioms S3131RegistryGateOwners_length
#print axioms S3131ABCStrengthResiduals_length
#print axioms LeanFormal.IUT.XiFPaper.S3140ThetaNormalizationLegActual.S3140LastSeamThetaMissing_iff_rawHaar
#print axioms LeanFormal.IUT.XiFPaper.S3140ThetaNormalizationLegActual.S3140MissingCanonicalRootedThetaReadout_of_factor_zero
#print axioms LeanFormal.IUT.XiFPaper.S3140ThetaNormalizationLegActual.S3140MissingThetaHalfReadout_of_factor_zero
#print axioms LeanFormal.IUT.XiFPaper.S3140ThetaNormalizationLegActual.S3140FourthTriangleResidual_of_normalization
#print axioms LeanFormal.IUT.XiFPaper.S3140NormalizedRootResidualActual.S3140NormalizedTwoLthRootSupply_iff

/-! ## Final residual registry checks (mainline task-49 handoff)

Canonical ids (task-53 dedupe): `R1.M2M3M5.sameC-q-theta-readout` is the single
canonical lattice readout id (object: SameCModelMapResidual /
SameCQThetaReadoutBridge; M0/M3 proved in qpilot S3133GaussianModelMapMinimal,
reduced residual GaussianR1ReducedResidual ↔ m1_indexInjection ∧ m2_baseQMatch).
`ThetaHalf.canonical-q-formula-gap` is the consumer of
`canonical.normalized-2l-root-supply`; `cusp.same-C-id` overlaps `R1.M0`
(keep the canonical ids; consumers depend on them). -/

/-- Registry has exactly 15 entries (14 base + hull ThetaHalf split into
`ThetaHalf.vform-canonical-residual` + `ThetaHalf.exact-factor-residual`). -/
example : S3131FinalResidualRegistry.length = 15 :=
  S3131FinalResidualRegistry_length

/-- Gate-owner dictionary has exactly 15 pairs. -/
example : S3131RegistryGateOwners.length = 15 :=
  S3131RegistryGateOwners_length

/-- The only ABC-strength residual id is F4.c.cardP-ABC-strength. -/
example : S3131ABCStrengthResiduals = ["F4.c.cardP-ABC-strength"] := rfl

/-- Every registry id appears in the gate-owner dictionary, in the same order
(the two lists are definitionally equal after projecting ids). -/
example : S3131FinalResidualRegistry.map (fun o => o.id) =
    S3131RegistryGateOwners.map Prod.fst := rfl

-- Computed audit checks (owner coverage and no dangling dependsOn ids); the
-- results are printed in the compile log as `true`.
#eval S3131FinalResidualRegistry.length
#eval S3131RegistryGateOwners.length
#eval S3131FinalResidualRegistry.all
  (fun o => (S3131RegistryGateOwners.map Prod.fst).contains o.id)
#eval S3131FinalResidualRegistry.all
  (fun o => o.dependsOn.all
    (fun d => (S3131FinalResidualRegistry.map (fun o => o.id)).contains d))

/-! ## Hull Theta-half residuals (task-41/58) and lattice canonical sub-residual index -/

#check LeanFormal.IUT.XiFPaper.S3132SharperThetaTargetReductionActual.MissingVFormCanonicalIdentification
#check LeanFormal.IUT.XiFPaper.S3132ThetaHalfResidualRegistryActual.ThetaHalfVFormCanonicalResidual
#check LeanFormal.IUT.XiFPaper.S3132ThetaHalfResidualRegistryActual.ThetaHalfExactFactorResidual
#check LeanFormal.IUT.XiFPaper.S3132ThetaHalfResidualRegistryActual.ThetaHalfRawResidual
#print axioms LeanFormal.IUT.XiFPaper.S3132ThetaHalfResidualRegistryActual.canonicalThetaTarget_of_VForm_and_exactFactor
#print axioms LeanFormal.IUT.XiFPaper.S3132ThetaHalfResidualRegistryActual.thetaHalfRawResidual_iff_missingThetaHalf
#print axioms LeanFormal.IUT.XiFPaper.S3132CanonicalVFormValueActual.S3134CanonicalRootedHC_eq_S3131CanonicalRootedHC
#print axioms LeanFormal.IUT.XiFPaper.S3132ThetaHalfDependencyChainActual.S3134LastSeamThetaHalf_iff_missingThetaHalf
#print axioms LeanFormal.IUT.XiFPaper.S3132GateThetaHalfConsumptionActual.missingThetaHalf_of_lastSeamThetaMissing
#print axioms LeanFormal.IUT.XiFPaper.S3132SharperThetaTargetReductionActual.MissingCanonicalRootedThetaReadout_of_factor_zero_and_VForm
#print axioms LeanFormal.IUT.XiFPaper.S3132SharperThetaTargetReductionActual.canonicalTarget_iff_factor_zero_of_VForm
#print axioms LeanFormal.IUT.XiFPaper.S3132SharperThetaTargetReductionActual.canonicalTarget_iff_factor_eq
-- Lattice canonical residual INDEX.* data files (S3137CanonicalResidualIndexActual /
-- Part2 / Part3 / Part4 / maintenance) are separate green data artifacts and are
-- deliberately NOT imported here: the acceptance gate's dependency closure stays
-- churn-free and fully fresh; INDEX.* ids are cited as data-only references.

/-! ## Lattice R1 canonical overlay and Theta-half normalization checks -/

#check S3137R1RegistryCanonical
#check S3137R1ConsumerEdges
#check S3137R1GreenConsumers
#check S3137R1FinalState
#check LeanFormal.IUT.XiFPaper.S3137GaussianR1ResidualLightActual.GaussianR1ReducedResidual
#check LeanFormal.IUT.XiFPaper.S3137C3TensorBlockDimensionActual.c3TensorBlockDimension_eq_prod_finrank
#check LeanFormal.IUT.XiFPaper.S3137R1ThetaHalfConsumerActual.thetaPilotHullLogVolumeReal_eq_log_paperHullRealLogVolume
#print axioms LeanFormal.IUT.XiFPaper.S3137GaussianR1ResidualLightActual.gaussianR1ReducedResidual_residual_iff
#print axioms LeanFormal.IUT.XiFPaper.S3137C3TensorBlockDimensionActual.c3TensorBlockDimension_eq_prod_finrank
#print axioms LeanFormal.IUT.XiFPaper.S3137R1ThetaHalfConsumerActual.thetaPilotHullLogVolumeReal_eq_log_paperHullRealLogVolume

/-! ## Residual structures / consumers recorded in this gate -/

#check LeanFormal.IUT.XiFPaper.S3135LogShellValueGroupActual.S3135PointLogShellFaithfulness
#check LeanFormal.IUT.XiFPaper.S3135ScalingNormalizationActual.S3135ScalingLogDegreeZero
#check LeanFormal.IUT.XiFPaper.S3135F5ActualReductionActual.S3135ActualPointWeightCard
#check LeanFormal.IUT.XiFPaper.S3132QThetaConsumerWiringActual.MissingC3ThetaHullReadoutIdentification
#check LeanFormal.IUT.XiFPaper.S3132CanonicalRootedThetaTargetActual.MissingCanonicalRootedThetaReadout
#check LeanFormal.IUT.XiFPaper.S3135HaarModulusActual.S3135AdditiveHaarModulusLaw
#check LeanFormal.IUT.XiFPaper.S3140ThetaNormalizationLegActual.S3140MissingThetaHalfReadout_of_factor_zero
#check LeanFormal.IUT.XiFPaper.S3140ThetaNormalizationLegActual.S3140FourthTriangleResidual_of_normalization
#check LeanFormal.IUT.XiFPaper.S3140NormalizedRootResidualActual.S3140NormalizedTwoLthRootSupply
#check LeanFormal.IUT.XiFPaper.S3137SameCModelMapResidualActual.SameCModelMapResidual
#check LeanFormal.IUT.XiFPaper.S3136LGPJvPacketTransportActual.LGPJvPacketTransportMissing
#check LeanFormal.IUT.XiFPaper.S3136LGPRealifiedValueTransportActual.LGPRealifiedValueTransportGap
#check LeanFormal.IUT.XiFPaper.S3136LGPLocalTensorPacketActual.LGPLocalPacketIdentificationGap
#check LeanFormal.IUT.XiFPaper.S3139FirstTriangleFieldBActual.sourceLGPData_thetaValueGenerator_mem

end
-- re-pinned against rebuilt S3131FinalResidualRegistryActual (EXIT=0 SIZE 9250, 15 ids, olean 03:17:01) + refreshed registry helpers (03:20:20); semantic no-change
-- FINAL registry re-pin: rebuilt S3131FinalResidualRegistryActual EXIT=0 SIZE 9528 (olean 03:23:47), 15 ids/order unchanged; semantic no-change, gate hashes re-pinned 2026-11-10

-- FINAL FINAL re-pin against registry SIZE 10039 (olean 03:24:43); gate hash pair for the acceptance record


-- FINAL freeze re-pin against registry SIZE 11034 (stepxi C2 theorem content update; olean 03:33:55, 15 ids/order/ABC unchanged)


-- REGISTRY FROZEN AT 11938 (src sha 002D6209..., olean 03:36:13): final acceptance re-pin


-- REGISTRY FROZEN AT 12702 (src sha 41C98036..., olean 03:38:48): THE final acceptance re-pin


-- ERRATA FROZEN AT 12847 (src sha 76809A6D..., olean 03:41:17; M2a OPEN): DEFINITIVE final acceptance pin


-- COMBINED REOPEN: C3 convention CLOSED (S3139C3ConventionClosureActual certified); registry 13108 frozen (olean 04:06:14) - single final re-pin


-- M2a CLOSED combined reopen (second real closure): registry SIZE 13129 (olean 04:19:43); single re-pin

