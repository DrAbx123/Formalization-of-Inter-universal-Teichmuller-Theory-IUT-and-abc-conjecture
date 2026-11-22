/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HaarStrictRPInstanceActual
import tmp.sheaf.xif.paper.Mzk1SignedCor312ContractActual
import Mathlib.Tactic

/-!
# Mzk1ScalingStrictChainActual — R/p scaling chain to signed Cor 3.12

A561: the `R/p` positive region scaled to the signed comparison:
`rpSignedQ = log μ(qRegionRP)`, `rpSignedTheta = log μ(hull)`; from the strict
Haar inequality (additivity step) the strict signed comparison follows by
`Real.log_lt_log`, and the `StepXIContract`/`Cor312Conclusion` assemble as before.
The strict Haar inequality is the single remaining named Haar fact, isolated as
`harStrictRP` hypothesis. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ScalingStrictChainActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarStrictRPInstanceActual
open LeanFormal.IUT.XiFPaper.Mzk1SignedCor312ContractActual
open MeasureTheory
open scoped ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The signed q reading of the `R/p` region. -/
noncomputable def rpSignedQ : Real :=
  Real.log (rootExtensionProductHaar T (qRegionRP T)).toReal

/-- The signed Theta reading of the hull. -/
noncomputable def rpSignedTheta : Real :=
  Real.log (rootExtensionProductHaar T (s1902Hull T)).toReal

/-- The q region has positive real Haar measure (proved). -/
theorem rpSignedQ_measure_pos :
    0 < (rootExtensionProductHaar T (qRegionRP T)).toReal :=
  ENNReal.toReal_pos (ne_of_gt (qRegionRP_measure_pos T))
    (ne_of_lt (qRegionRP_measure_lt_top T))

/-- Strict signed comparison from the strict Haar inequality. -/
theorem rpSigned_strict
    (h : (rootExtensionProductHaar T (qRegionRP T)).toReal <
      (rootExtensionProductHaar T (s1902Hull T)).toReal) :
    rpSignedQ T < rpSignedTheta T :=
  Real.log_lt_log (rpSignedQ_measure_pos T) h

/-- Non-strict signed comparison from the strict one. -/
theorem rpSigned_le
    (h : (rootExtensionProductHaar T (qRegionRP T)).toReal <
      (rootExtensionProductHaar T (s1902Hull T)).toReal) :
    rpSignedQ T ≤ rpSignedTheta T :=
  le_of_lt (rpSigned_strict T h)

/-- The assembled contract from the `R/p` region (strict Haar hypothesis isolated). -/
noncomputable def rpContract
    (harStrictRP : (rootExtensionProductHaar T (qRegionRP T)).toReal <
      (rootExtensionProductHaar T (s1902Hull T)).toReal)
    (hqneg : rpSignedQ T < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) : StepXIContract :=
  signedCor312Contract (rpSignedQ T) (rpSignedTheta T) hqneg
    ipl hipl she hshe apt hapt (rpSigned_le T harStrictRP)

/-- Cor 3.12 conclusion from the `R/p` region (strict Haar hypothesis isolated). -/
theorem rpContract_cor312
    (harStrictRP : (rootExtensionProductHaar T (qRegionRP T)).toReal <
      (rootExtensionProductHaar T (s1902Hull T)).toReal)
    (hqneg : rpSignedQ T < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion (rpContract T harStrictRP hqneg ipl hipl she hshe apt hapt) :=
  signedCor312_conclusion (rpSignedQ T) (rpSignedTheta T) hqneg
    ipl hipl she hshe apt hapt (rpSigned_le T harStrictRP)

#check rpSigned_strict
#check rpContract_cor312

end LeanFormal.IUT.XiFPaper.Mzk1ScalingStrictChainActual
end
