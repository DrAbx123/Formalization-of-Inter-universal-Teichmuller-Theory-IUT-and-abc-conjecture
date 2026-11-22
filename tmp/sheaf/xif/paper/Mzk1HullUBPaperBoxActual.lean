/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1MainTermActualBoundActual
import tmp.sheaf.xif.paper.Mzk1StepVVolumeUpperActual
import Mathlib.Tactic
/-! # GAP-P7-HULL-UB: actual normalizedLog hull <= paperBox(disc,cond,0) -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1HullUBPaperBoxActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1ExactHullVMainTermActual
open LeanFormal.IUT.XiFPaper.Mzk1MainTermActualBoundActual
open LeanFormal.IUT.XiFPaper.Mzk1MainTermActualNonnegActual
open LeanFormal.IUT.XiFPaper.Mzk1StepVVolumeUpperActual
open LeanFormal.IUT.XiFPaper.Mzk1P3DictDCurveDataSourceActual
open LeanFormal.IUT.XiFPaper.Mzk1P3DictDLogDiscActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open MeasureTheory
universe u
variable {l : PrimeGeFive} {ι : Type u}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
theorem normalizedLog_hull_le_paperBox (M : CurveData ι) (E : ι) :
    rootExtensionProductNormalizedLog T (s1902Hull T) ≤
      paperBox (l.value : Real) (Real.log (M.disc E : Real))
        (Real.log (M.cond E : Real)) 0 := by
  have h := normalizedLog_hull_le_actualMainTerm (T := T) (l := l) M E
  have hd : 0 ≤ Real.log (M.disc E : Real) := log_natCast_nonneg _
  have hf : 0 ≤ Real.log (M.cond E : Real) := log_natCast_nonneg _
  have hsum : 0 ≤ Real.log (M.disc E : Real) + Real.log (M.cond E : Real) :=
    add_nonneg hd hf
  have hl : 0 ≤ (l.value : Real) := by exact_mod_cast Nat.zero_le l.value
  have hcoef : (1 / 4 : Real) * (l.value : Real) ≤ ((l.value : Real) + 5) / 4 := by
    nlinarith
  have hstep : (1 / 4 : Real) * (l.value : Real) *
      (Real.log (M.disc E : Real) + Real.log (M.cond E : Real)) ≤
      ((l.value : Real) + 5) / 4 *
        (Real.log (M.disc E : Real) + Real.log (M.cond E : Real)) := by
    exact mul_le_mul_of_nonneg_right hcoef hsum
  rw [paperBox_eq]
  simpa using h.trans hstep
def rows : List String := ["normalizedLog_hull_le_actualMainTerm", "coefficient (1/4)l <= (l+5)/4", "paperBox C0=0"]
theorem rows_length : rows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1HullUBPaperBoxActual
end