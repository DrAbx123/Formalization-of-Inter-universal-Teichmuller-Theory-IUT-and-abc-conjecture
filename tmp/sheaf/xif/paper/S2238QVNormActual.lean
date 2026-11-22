import tmp.sheaf.xif.paper.S2230QVLogKummerActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedIntegers
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion

/-! # S2238: norm comparison and q_v properties in the integral closure

`normalizedCompletion_norm_lt_one_iff` compares the completion norm with the
normalized spectral norm.  This lets us transport the S2092 q_v estimate to the
S2147 integral closure and prove q_v nonzero/integral/norm<1. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2238QVNormActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual
open LeanFormal.IUT.XiFPaper.S2147PaperIntegralClosureOUnitsActionActual
open LeanFormal.IUT.XiFPaper.S2092PaperOtriActual
open LeanFormal.IUT.XiFPaper.S2219PaperOUnitsCarrierActual
open LeanFormal.IUT.XiFPaper.S2230QVLogKummerActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The normalized-completion representative of the paper q_v. -/
noncomputable def s2238x : NormalizedCompletion (sectionKPlace T b) :=
  (normalizedCompletionRingEquiv (sectionKPlace T b)).symm
    (((paperQV T b : paperOtri T b) : paperKv T b))

theorem s2238x_norm_lt_one : ‖s2238x T b‖ < 1 := by
  apply (normalizedCompletion_norm_lt_one_iff (sectionKPlace T b) (s2238x T b)).mp
  have h : normalizedCompletionRingEquiv (sectionKPlace T b) (s2238x T b) =
      ((paperQV T b : paperOtri T b) : paperKv T b) :=
    RingEquiv.apply_symm_apply _ _
  simpa [h] using paperQV_norm_lt_one T b

/-- The integral-closure q_v candidate built from the normalized representative. -/
noncomputable def s2238qv : S2147PaperIntegralClosure T b :=
  algebraMap (NormalizedCompletion (sectionKPlace T b))
    (S2147PaperIntegralClosure T b) (s2238x T b)

theorem s2238qv_norm_lt_one : ‖s2238qv T b‖ < 1 := by
  rw [s2238qv, norm_algebraMap']
  exact s2238x_norm_lt_one T b

theorem s2238qv_integral :
    s2238qv T b ∈ Integers (S2147PaperIntegralClosure T b) := by
  rw [mem_integers_iff]
  exact le_of_lt (s2238qv_norm_lt_one T b)

theorem s2238qv_ne_zero : s2238qv T b ≠ 0 := by
  intro h
  have hx0 : s2238x T b = 0 :=
    (algebraMap (NormalizedCompletion (sectionKPlace T b))
      (S2147PaperIntegralClosure T b)).injective (by simpa [s2238qv] using h)
  have hpaper0 : ((paperQV T b : paperOtri T b) : paperKv T b) = 0 := by
    have := congrArg (normalizedCompletionRingEquiv (sectionKPlace T b)) hx0
    simpa [s2238x] using this
  have hq : ((paperQV T b : paperOtri T b) : paperKv T b) ≠ 0 := by
    rw [paperQV_val]
    exact (sectionQ T b).q_ne_zero
  exact hq hpaper0

/-- Exact remaining logKummer compatibility datum. -/
structure S2238LogKummerRequired
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  logKummer : S2219PaperOUnits T b →* S2219PaperOUnits T b
  logKummer_qv_compatible : Prop

def S2238LogKummerRequiredProp
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Prop :=
  Nonempty (S2238LogKummerRequired T b)

#check s2238x_norm_lt_one
#check s2238qv_norm_lt_one
#check s2238qv_integral
#check s2238qv_ne_zero
#check S2238LogKummerRequired

end LeanFormal.IUT.XiFPaper.S2238QVNormActual
end
