/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P7ContractMapActual
import tmp.sheaf.xif.paper.Mzk1P7ComparisonConditionalFinalActual
import Mathlib.Tactic

/-! # P7/#8 consumer entry: margin-1 condition for the conditional contract -/

/-
| field | value |
|---|---|
| Status | PROVED consumer wrappers: `qread + 1 <= thetaRead` (or `HullQDictionary`) directly feeds `p7_conditional_contract`; no new assumption |
| GAP | GAP-P7-CONTRACT remains CONDITIONAL: the margin/dictionary witness is still a named input; the other 6 missing rows unchanged |
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P7ContractMarginConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.Mzk1P7GapRegisterActual
open LeanFormal.IUT.XiFPaper.Mzk1P7ContractMapActual
open LeanFormal.IUT.XiFPaper.Mzk1P7ComparisonConditionalFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312S3137AssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1S1915ComparisonActual
open MeasureTheory
open scoped ENNReal BigOperators

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- **Margin-1 condition directly implies the comparison**: `qread + 1 <= thetaRead`. -/
theorem comparison_of_margin_one
    (hmargin : qPilotLogVolumeReading P + 1 ≤ thetaPilotHullLogVolumeReal C3) :
    qThetaPilotLogVolumeComparison C3 P := by
  unfold qThetaPilotLogVolumeComparison
  linarith

/-- Margin-1 form of the theta−q gap (from the dictionary). -/
theorem margin_one_theta_sub (D : HullQDictionary T C3 P) :
    thetaPilotHullLogVolumeReal C3 - qPilotLogVolumeReading P = 1 := by
  rw [theta_read_eq_qRead_add_one T C3 P D]
  ring

/-- **#8 mainline consumer (margin form)**: a margin-1 witness feeds the conditional
contract assembly directly. -/
theorem p7_conditional_contract_of_margin_one
    (hmargin : qPilotLogVolumeReading P + 1 ≤ thetaPilotHullLogVolumeReal C3) :
    Cor312Conclusion
      (contractOfS3137Comparison C3 P (comparison_of_margin_one C3 P hmargin)) :=
  cor312_of_s3137Comparison C3 P (comparison_of_margin_one C3 P hmargin)

/-- **#8 mainline consumer (dictionary form)**: the two-field dictionary feeds the
conditional contract assembly without a separate comparison argument. -/
theorem p7_conditional_contract_of_hullQDictionary (D : HullQDictionary T C3 P) :
    Cor312Conclusion
      (contractOfS3137Comparison C3 P (comparison_of_hullQDictionary T C3 P D)) :=
  cor312_of_s3137Comparison C3 P (comparison_of_hullQDictionary T C3 P D)

/-- Condition evidence rows for the 7 missing items, aligned with `missing7ToGap`. -/
def margin7Rows : List (String × String × String) :=
  [ ("general qThetaPilotLogVolumeComparison", "GAP-P7-GENERAL-CMP",
      "HullQDictionary (theta_eq+q_eq_sum) or margin qread+1<=thetaRead; comparison PROVED conditional")
  , ("paper carrier IQ realization", "GAP-P7-IQ-LITERAL", "definition-level discharged; paper-literal structures open")
  , ("(Ob3-3) source identification", "GAP-P7-OB33-SRC", "conditional")
  , ("multiradial (xi-e)/(xi-f) production", "GAP-P7-MULTIRADIAL", "partial")
  , ("theta raw Haar vs paper normalized V", "GAP-P7-THETA-V / GAP-P7-THETA-D / GAP-P7-THETA-DEG", "#5 discharged; #6/#7 partial")
  , ("StepXIContract fields/linkage", "GAP-P7-CONTRACT", "ContractFieldsLinked=false; conditional assembly")
  , ("exact hull volume upper bound", "GAP-P7-HULL-UB", "paper regime discharged; general disc=1 open") ]

theorem margin7Rows_length : margin7Rows.length = 7 := rfl


end LeanFormal.IUT.XiFPaper.Mzk1P7ContractMarginConsumerActual