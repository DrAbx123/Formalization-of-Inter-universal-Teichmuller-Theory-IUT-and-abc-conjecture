/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HullUBPaperVRawBindingActual
import tmp.sheaf.xif.paper.Mzk1HullUBPaperBoxActual
import tmp.sheaf.xif.paper.Mzk1HullUBPaperVRawBindingActual
import Mathlib.Tactic
/-! # GAP-P7-HULL-UB B6: paper closed-form V upper bound with C0=1 -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1HullUBPaperVRawUpperActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1HullUBPaperBoxActual
open LeanFormal.IUT.XiFPaper.Mzk1HullUBPaperBoxActual
open LeanFormal.IUT.XiFPaper.Mzk1HullUBPaperVRawBindingActual
open LeanFormal.IUT.XiFPaper.Mzk1P3DictDCurveDataSourceActual
open LeanFormal.IUT.XiFPaper.Mzk1StepVVolumeUpperActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open MeasureTheory
universe u
variable {l : PrimeGeFive} {ι : Type u}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
theorem paperV_closedForm_le_paperBox_add_one (M : CurveData ι) (E : ι) :
    s1915ClosedForm T ≤
      paperBox (l.value : Real) (Real.log (M.disc E : Real))
        (Real.log (M.cond E : Real)) 0 + 1 := by
  have hraw : s1915ClosedForm T = 1 + rootExtensionProductNormalizedLog T (s1902Hull T) :=
    closedForm_eq_one_add_normalizedLog (T := T)
  have hnorm := normalizedLog_hull_le_paperBox (T := T) (l := l) M E
  linarith
def rows : List String := ["rawV <= paperBox + 1", "C0=1", "actual B6 bound"]
theorem rows_length : rows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1HullUBPaperVRawUpperActual
end