/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1PositiveMeasureSignedConsumerActual
import tmp.sheaf.xif.paper.Mzk1AxiomGateActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.S1929LiteralIQCarrierActual

/-! # Mzk1PositiveMeasureAcceptanceActual — acceptance over the green half-ball consumer

A570 (qpilot lane, non-conflicting name): acceptance checks over the green
positive-measure half-ball qRegion consumer and the axiom gate.
 -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1PositiveMeasureAcceptanceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1PositiveMeasureSignedConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1AxiomGateActual
open MeasureTheory
open scoped ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Acceptance: the half-ball qRegion normalized volume is exactly 1. -/
theorem acceptance_qRegion_normalized :
    qNormalizedVolume T (qRegion T) = 1 :=
  qNormalizedVolume_qRegion_eq T

/-- Acceptance: strict Haar increase implies the strict normalized comparison. -/
theorem acceptance_strict_implies_signed
    (h : (rootExtensionProductHaar T (qRegion T)).toReal <
      (rootExtensionProductHaar T (s1902Hull T)).toReal) :
    qNormalizedVolume T (qRegion T) < qNormalizedVolume T (s1902Hull T) :=
  qNormalizedVolume_strict T h

/-- Acceptance: the Cor 3.12 conclusion from the half-ball consumer. -/
theorem acceptance_cor312
    (h : (rootExtensionProductHaar T (qRegion T)).toReal <
      (rootExtensionProductHaar T (s1902Hull T)).toReal)
    (hqneg : qNormalizedVolume T (qRegion T) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (qRegionContract T h hqneg ipl hipl she hshe apt hapt) :=
  qRegionContract_cor312 T h hqneg ipl hipl she hshe apt hapt

#check acceptance_qRegion_normalized
#check acceptance_cor312

end LeanFormal.IUT.XiFPaper.Mzk1PositiveMeasureAcceptanceActual
end
