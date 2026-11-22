/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ThetaVGeneralUnconditionalActual
import tmp.sheaf.xif.paper.Mzk1ScaledThetaHullNormalizedLogShaActual
import Mathlib.Tactic
/-! # GAP-P7-HULL-UB general-k final upper bound (C0=1, no arch term) -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1HullUBGeneralFinalActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1ThetaVGeneralUnconditionalActual
open LeanFormal.IUT.XiFPaper.Mzk1P3DictDCurveDataSourceActual
open LeanFormal.IUT.XiFPaper.Mzk1StepVVolumeUpperActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullShaActual
open LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullNormalizedLogShaActual
open MeasureTheory
universe u
variable {l : PrimeGeFive} {ι : Type u}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
theorem generalK_paperV_eq (k : ℕ) :
    scaledClosedFormR T (k : Real) =
      rootExtensionProductNormalizedLog T (scaledThetaHull T k) + 1 := by
  have h := scaledThetaHull_normalizedLog_eq (T := T) k
  linarith
theorem generalK_final_upper (M : CurveData ι) (E : ι) (k : ℕ) :
    scaledClosedFormR T (k : Real) ≤
      paperBox (l.value : Real) (Real.log (M.disc E : Real))
        (Real.log (M.cond E : Real)) 0 + 1 := by
  exact scaledClosedFormR_le_paperBox_add_one (T := T) (l := l) M E k
theorem generalK_final_upper_C0_one (M : CurveData ι) (E : ι) (k : ℕ) :
    scaledClosedFormR T (k : Real) ≤
      paperBox (l.value : Real) (Real.log (M.disc E : Real))
        (Real.log (M.cond E : Real)) 1 := by
  rw [Mzk1StepVVolumeUpperActual.paperBox_eq]
  have h := generalK_final_upper (T := T) (l := l) M E k
  rw [Mzk1StepVVolumeUpperActual.paperBox_eq] at h
  linarith
def rows : List String := ["V_paper(k)=scaledClosedFormR k", "V_paper=normalizedLog+1", "V_paper<=paperBox+1 (C0=1)", "no arch term: only finite disc/cond"]
theorem rows_length : rows.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1HullUBGeneralFinalActual
end