/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HullUBPaperVRawBindingActual
import tmp.sheaf.xif.paper.Mzk1HullUBPaperVRawUpperActual
import tmp.sheaf.xif.paper.Mzk1ExactHullVMainTermActual
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
/-! # GAP-P7-HULL-UB: C0=0 under paper regime (disc>=2, cond>=1, l>=5) -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1HullUBC0AbsorptionActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1HullUBPaperVRawBindingActual
open LeanFormal.IUT.XiFPaper.Mzk1ExactHullVMainTermActual
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
theorem box_ge_one_of_disc_ge_two_cond_ge_one
    (M : CurveData ι) (E : ι) (hd : 2 ≤ M.disc E) (hf : 1 ≤ M.cond E) :
    1 ≤ paperBox (l.value : Real) (Real.log (M.disc E : Real))
      (Real.log (M.cond E : Real)) 0 := by
  rw [Mzk1StepVVolumeUpperActual.paperBox_eq]
  have hl : (5 : Real) ≤ (l.value : Real) := by exact_mod_cast l.ge_five
  have hld : Real.log 2 ≤ Real.log (M.disc E : Real) := by
    apply Real.log_le_log (by norm_num) (by exact_mod_cast hd)
  have hlf : 0 ≤ Real.log (M.cond E : Real) :=
    Real.log_nonneg (by exact_mod_cast hf)
  have hcoef : (5 / 2 : Real) ≤ ((l.value : Real) + 5) / 4 := by nlinarith
  have hsum : Real.log 2 ≤ Real.log (M.disc E : Real) + Real.log (M.cond E : Real) :=
    by linarith
  have hmul : (5 / 2 : Real) * Real.log 2 ≤
      ((l.value : Real) + 5) / 4 *
        (Real.log (M.disc E : Real) + Real.log (M.cond E : Real)) := by
    exact mul_le_mul hcoef hsum (by positivity) (by nlinarith)
  have hnum : 1 ≤ (5 / 2 : Real) * Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  linarith
theorem paperV_le_paperBox_zero_of_box_ge_one
    (M : CurveData ι) (E : ι)
    (hbox : 1 ≤ paperBox (l.value : Real) (Real.log (M.disc E : Real))
      (Real.log (M.cond E : Real)) 0) :
    s1915ClosedForm T ≤ paperBox (l.value : Real) (Real.log (M.disc E : Real))
      (Real.log (M.cond E : Real)) 0 := by
  have hraw := closedForm_eq_one_add_normalizedLog (T := T)
  have hnorm := normalizedLog_hull_nonpos (T := T)
  linarith
theorem paperV_le_paperBox_zero_of_disc_ge_two_cond_ge_one
    (M : CurveData ι) (E : ι) (hd : 2 ≤ M.disc E) (hf : 1 ≤ M.cond E) :
    s1915ClosedForm T ≤ paperBox (l.value : Real) (Real.log (M.disc E : Real))
      (Real.log (M.cond E : Real)) 0 := by
  exact paperV_le_paperBox_zero_of_box_ge_one (T := T) (l := l) M E
    (box_ge_one_of_disc_ge_two_cond_ge_one (l := l) M E hd hf)
def rows : List String := ["norm <= 0", "paper regime => paperBox >= 1", "C0=0 under disc>=2 & cond>=1 & l>=5"]
theorem rows_length : rows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1HullUBC0AbsorptionActual
end