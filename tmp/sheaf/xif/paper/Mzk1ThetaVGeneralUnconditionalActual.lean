/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ScaledThetaHullShaActual
import tmp.sheaf.xif.paper.Mzk1ScaledThetaHullNormalizedLogShaActual
import tmp.sheaf.xif.paper.Mzk1HullUBPaperVRawUpperActual
import tmp.sheaf.xif.paper.Mzk1ThetaVLayerScaleOffsetActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import Mathlib.Tactic
/-! # GAP-P7-THETA-V L4: unconditional general-k scale/offset and C0=1 bound -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaVGeneralUnconditionalActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullShaActual
open LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullNormalizedLogShaActual
open LeanFormal.IUT.XiFPaper.Mzk1HullUBPaperVRawUpperActual
open LeanFormal.IUT.XiFPaper.Mzk1ThetaVLayerScaleOffsetActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1HullUBPaperVRawBindingActual
open LeanFormal.IUT.XiFPaper.Mzk1HullUBPaperBoxActual
open LeanFormal.IUT.XiFPaper.Mzk1P3DictDCurveDataSourceActual
open LeanFormal.IUT.XiFPaper.Mzk1StepVVolumeUpperActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open MeasureTheory
open scoped BigOperators
universe u
variable {l : PrimeGeFive} {ι : Type u}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
instance badNonempty : Nonempty (Bad (nativePlaceSelection T)) := by
  rcases (nativePlaceSelection T).V_mod_bad_nonempty with ⟨p, hp⟩
  exact ⟨⟨p, hp⟩⟩
theorem qLogSum_nonneg : 0 ≤ qLogSum T := by
  unfold qLogSum
  apply Finset.sum_nonneg
  intro b _
  apply mul_nonneg (by exact_mod_cast Nat.zero_le (s1915LocalDegree T b))
  exact Real.log_nonneg (by exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).one_lt.le)
noncomputable def thetaVScaleOffsetGeneral (k : ℕ) : ThetaVScaleOffset where
  rawV := scaledClosedFormR T (k : ℝ)
  normV := rootExtensionProductNormalizedLog T (scaledThetaHull T k)
  scale := 1
  scale_pos := by norm_num
  offset := 1
  layer_eq := by
    have h := scaledThetaHull_normalizedLog_eq (T := T) k
    linarith
theorem thetaVScaleOffsetGeneral_scale (k : ℕ) :
    (thetaVScaleOffsetGeneral (T := T) k).scale = 1 := rfl
theorem thetaVScaleOffsetGeneral_offset (k : ℕ) :
    (thetaVScaleOffsetGeneral (T := T) k).offset = 1 := rfl
theorem scaledClosedFormR_le_s1915 (k : ℕ) :
    scaledClosedFormR T (k : ℝ) ≤ s1915ClosedForm T := by
  rw [scaledClosedFormR_eq]
  have hk : (0 : Real) ≤ (k : Real) := by exact_mod_cast Nat.zero_le k
  nlinarith [qLogSum_nonneg (T := T)]
theorem scaledClosedFormR_le_paperBox_add_one (M : CurveData ι) (E : ι) (k : ℕ) :
    scaledClosedFormR T (k : ℝ) ≤
      paperBox (l.value : Real) (Real.log (M.disc E : Real))
        (Real.log (M.cond E : Real)) 0 + 1 := by
  exact (scaledClosedFormR_le_s1915 (T := T) k).trans
    (paperV_closedForm_le_paperBox_add_one (T := T) (l := l) M E)
def rows : List String := ["general-k ThetaVScaleOffset: rawV=scaledClosedFormR k, scale=1, offset=1", "qLogSum_nonneg", "scaledClosedFormR k <= s1915ClosedForm", "scaledClosedFormR k <= paperBox+1 (C0=1)"]
theorem rows_length : rows.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1ThetaVGeneralUnconditionalActual
end