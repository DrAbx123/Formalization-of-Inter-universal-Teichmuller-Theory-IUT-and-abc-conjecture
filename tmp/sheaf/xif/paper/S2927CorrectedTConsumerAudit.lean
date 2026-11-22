import LeanFormal.IUT.IUTI.InitialTheta.SourceCompletion
import LeanFormal.IUT.IUTI.InitialTheta.SourceClauseConstructors
import LeanFormal.IUT.IUTI.HodgeTheater.SourceClauseAssemblyUnitsReduction
import tmp.sheaf.xif.paper.S2482CorrectedSourceSignQuotientActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2482CorrectedSourceSignQuotientActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2927CorrectedTConsumerAudit

/-!
## S2927 audit: T consumers of SourceCompletion

### Record definition and fields

SourceCompletion (LeanFormal/IUT/IUTI/InitialTheta/SourceCompletion.lean)
contains, among others:

* arithmetic : InitialThetaArithmeticData l
* sourceSignQuotientData : SourceSignQuotientData arithmetic
  (the old record with the false strong unique_elliptic_involution field)
* sourceClauseA/B/C/D/E/F depending on that old S
* cK/cF and epsilon fields derived from the old S
* nativeInitialThetaData / sourceNative / clause assembly fields.

The T-relevant consumers read:
  C.sourceSignQuotientData.cK, C.sourceSignQuotientData.cF,
  C.sourceSignQuotientData.epsilon, C.sourceSignQuotientData.V,
  C.sourceSignQuotientData.V_mod_bad, C.sourceSignQuotientData.xK, ...

### IUTI consumers (must switch to SourceCompletionCorrected)

Record-defining and clause files:
* IUTI/InitialTheta/SourceCompletion.lean
* IUTI/InitialTheta/SourceClauseConstructors.lean
* IUTI/InitialTheta/SourceDefinition31Quantifiers.lean
* IUTI/InitialTheta/SourceSignQuotientConstruction.lean
* IUTI/InitialTheta/SourceDefinition31LocalValuationSections.lean
* IUTI/InitialTheta/SourcePlaceQParameterUniformization.lean
* IUTI/InitialTheta/SourcePlaceTateComparisonSynthesis.lean
* IUTI/InitialTheta/SourceTorsionCarrierReduction.lean
* IUTI/HodgeTheater/SourceClauseAssemblyUnitsReduction.lean
* IUTI/HodgeTheater/SourceDefinition31NativeContractBridgeReduction.lean
* IUTI/HodgeTheater/SourceDefinition31SignQuotientSupplyReduction.lean

### XiFPaper T-consumers of SourceCompletion / sourceSignQuotientData

* S2171SourceCompletionActual.lean
* S2757SourceCompletionNativeActual.lean
* S1494NativeArithmeticRootActual.lean
* S1519NativeThetaConcreteActual.lean
* S1532PaperNativeRootActual.lean
* S1633SignQuotientBasicActual.lean
* S1636SourceClausesActual.lean
* S1983EtThSignatureBridgeActual.lean
* S1989KSideCoverActual.lean
* S1994KSideCoversActual.lean
* S2043D9FullActual.lean
* S2482CorrectedSourceSignQuotientActual (corrected definition)
* S2555D8CuspidalDecompositionActual.lean
* S2616CuspAssemblyActual.lean
* S2617CuspClauseReductionActual.lean
* S2617CuspParameterCandidateActual.lean
* S2618CuspUniformizerNoGoActual.lean
* S2618LocalModelActual.lean
* S2619CuspUniformizerActual.lean
* S2684BadPlaceContractConditionalActual.lean
* S2753CarrierTransportActual.lean
* S2773ClauseAConditionalActual.lean
* S2774ClauseCFromDataActual.lean
* S2786SignQuotientActual.lean
* S2787ClauseB37Actual.lean
* S2797ClauseA37ConditionalActual.lean
* S2805ClauseBFullConditional.lean
* ClauseEToD7Actual.lean, ClauseEToD7LocalGroupActual.lean
* CuspCoordinateSearchActual.lean, CuspFromSourceClauseActual.lean,
  CuspRealizationActual.lean
* LocalGroupBijectionActual.lean
* NativeCuspCountActual.lean, NativeCuspRealActual.lean,
  NativeD7CuspActual.lean, NativeSourceAssemblyReusableActual.lean
* NativeSourceTorsionGapsActualConstruction.lean, NativeTorsionGapsActual.lean,
  NativeTorsionGapsActualField.lean, NativeTorsionGapsIntegration.lean
* S1330CuspEpsilonActual.lean, S1357RealCuspCoordinateActual.lean,
  S1360D9OrbicurveSlotActual.lean, S1370SourceSignQuotientFix.lean,
  S1374SourceSignQuotientFix.lean, S1376PaperKCoreRestatementActual.lean,
  S1383RealCuspCoordinateActual.lean, S1387D9PaperSlotActual.lean,
  S1400RealCuspCoordinateActual.lean, S1403D789SupplyActual.lean,
  S1428RealCuspValuationActual.lean

### IUTII/III/IV

A direct search for the old record SourceCompletion in IUTII/III/IV finds no
consumer of the InitialThetaSource.SourceCompletion record.  IUTIII
Theorem311.SourceCompletionK1K2Wiring uses a different local structure
SourceTheorem311Completion, not the InitialThetaSource record, so it is not in
the corrected-T list.

### Fields that must change

For every consumer above, the fields that must be re-typed are exactly:
* C.sourceSignQuotientData : SourceSignQuotientDataCorrected C.arithmetic
* all projections C.sourceSignQuotientData.{cK,cF,xK,xF,V,V_mod_bad,
  V_mod_bad_odd_residue_characteristic,V_mod_bad_nonempty,V_section,
  V_eq_section,V_mod_bijection,V_place_comap,epsilon}
* the old strong unique_elliptic_involution must disappear; the corrected
  record's weakened unique field replaces it.

No corrected SourceCompletion exists yet; the corrected record
SourceSignQuotientDataCorrected exists (S2482).  No consumer is claimed
finished.  No fake completion is introduced.
-/

#check LeanFormal.IUT.InitialThetaSource.SourceCompletion
#check LeanFormal.IUT.InitialThetaSource.SourceSignQuotientData
#check LeanFormal.IUT.XiFPaper.S2482CorrectedSourceSignQuotientActual.SourceSignQuotientDataCorrected
#check LeanFormal.IUT.InitialThetaSource.SourceCompletion.sourceSignQuotientData

end LeanFormal.IUT.XiFPaper.S2927CorrectedTConsumerAudit
end
