/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1MainTermActualBoundActual
import tmp.sheaf.xif.paper.Mzk1StepVVolumeUpperActual
import tmp.sheaf.xif.paper.Mzk1PaperNormalizationRawVsNormalizedActual
import Mathlib.Tactic
/-! # GAP-P7-HULL-UB: dictionary from normalizedLog bound to paper V (self-contained) -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1HullUBDictionaryActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1ExactHullVMainTermActual
open LeanFormal.IUT.XiFPaper.Mzk1MainTermActualBoundActual
open LeanFormal.IUT.XiFPaper.Mzk1MainTermActualNonnegActual
open LeanFormal.IUT.XiFPaper.Mzk1StepVVolumeUpperActual
open LeanFormal.IUT.XiFPaper.Mzk1P3DictDCurveDataSourceActual
open LeanFormal.IUT.XiFPaper.Mzk1P3DictDLogDiscActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperNormalizationRawVsNormalizedActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open MeasureTheory
universe u
variable {l : PrimeGeFive} {ι : Type u}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
theorem normalizedLog_hull_le_paperBox_local (M : CurveData ι) (E : ι) :
    rootExtensionProductNormalizedLog T (s1902Hull T) ≤
      Mzk1StepVVolumeUpperActual.paperBox (l.value : Real) (Real.log (M.disc E : Real))
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
  rw [Mzk1StepVVolumeUpperActual.paperBox_eq]
  simpa using h.trans hstep
structure HullUBDictionaryData (M : CurveData ι) (E : ι) where
  dict : RawNormalizedDictionary
  normV_eq : dict.normV = rootExtensionProductNormalizedLog T (s1902Hull T)
theorem paperV_le_of_dictionary (M : CurveData ι) (E : ι)
    (D : HullUBDictionaryData (T := T) M E)
    (hscale : D.dict.scale = 1) (hoffset : D.dict.offset = 0) :
    D.dict.rawV ≤ Mzk1StepVVolumeUpperActual.paperBox (l.value : Real) (Real.log (M.disc E : Real))
      (Real.log (M.cond E : Real)) 0 := by
  have h := normalizedLog_hull_le_paperBox_local (T := T) (l := l) M E
  rw [← D.normV_eq] at h
  rw [D.dict.dict_eq, hscale, hoffset]
  simpa using h
def rows : List String := ["normalizedLog <= Mzk1StepVVolumeUpperActual.paperBox (local proof)", "dict.normV=normalizedLog", "paperV <= paperBox"]
theorem rows_length : rows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1HullUBDictionaryActual
end