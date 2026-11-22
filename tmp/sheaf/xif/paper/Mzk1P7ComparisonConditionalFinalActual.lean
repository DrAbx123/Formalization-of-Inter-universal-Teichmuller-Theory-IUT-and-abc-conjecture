/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1S1915ComparisonActual
import Mathlib.Tactic

/-! # P7/#1 final conditional form: `HullQDictionary` is the only named input -/

/-
| field | value |
|---|---|
| Status | CONDITIONAL: `HullQDictionary T C3 P → qThetaPilotLogVolumeComparison C3 P` (margin 1); `HullQDictionary` = theta_eq + q_eq_sum, the two scalar same-origin alignments |
| GAP | the dictionary itself; (a) baseQ↔qVFamily, (b) ∏ qVFamNormRatio=1 (source-field obstruction), (c) place-sum identity are its precise sub-obstacles; no new assumption added here |
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P7ComparisonConditionalFinalActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.Mzk1S1915ComparisonActual
open LeanFormal.IUT.XiFPaper.Mzk1Paper312StatementActual
open LeanFormal.IUT.XiFPaper.Mzk1N3SharedContainerRealActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open MeasureTheory
open scoped ENNReal BigOperators

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- **Final conditional #1**: the two-field dictionary implies the comparison (margin 1). -/
theorem comparison_of_hullQDictionary (D : HullQDictionary T C3 P) :
    qThetaPilotLogVolumeComparison C3 P :=
  qThetaPilotLogVolumeComparison_of_s1915 T C3 P D

/-- Under the dictionary the theta read is exactly `qRead + 1` (strict margin 1). -/
theorem theta_read_eq_qRead_add_one (D : HullQDictionary T C3 P) :
    thetaPilotHullLogVolumeReal C3 = qPilotLogVolumeReading P + 1 := by
  rw [D.theta_eq, s1915ClosedForm_eq_one_add_qReading T C3 P D]
  ring

/-- Strict margin-1 form of the comparison: `qRead + 1 <= thetaRead`. -/
theorem comparison_margin_one (D : HullQDictionary T C3 P) :
    qPilotLogVolumeReading P + 1 ≤ thetaPilotHullLogVolumeReal C3 := by
  rw [theta_read_eq_qRead_add_one T C3 P D]

/-- Boundary form: `paperGap` on any real shared container follows from the dictionary. -/
theorem paperGap_of_hullQDictionary (D : HullQDictionary T C3 P)
    (Dc : SharedContainerReal (l := l) (I := I) C3 P) : paperGap Dc :=
  paperGap_of_s1915 T C3 P D Dc

/-- Row summary of the final conditional form. -/
def rows : List (String × String × String) :=
  [ ("named input", "HullQDictionary (theta_eq + q_eq_sum)", "CONDITIONAL")
  , ("comparison", "HullQDictionary -> qThetaPilotLogVolumeComparison", "PROVED (margin 1)")
  , ("margin", "thetaRead = qRead + 1", "PROVED")
  , ("paperGap", "HullQDictionary -> paperGap (any shared container)", "PROVED")
  , ("sub-obstacles", "baseQ<->qVFamily; prodb qVFamNormRatio=1; place-sum identity", "GAP (source fields)") ]

theorem rows_length : rows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P7ComparisonConditionalFinalActual