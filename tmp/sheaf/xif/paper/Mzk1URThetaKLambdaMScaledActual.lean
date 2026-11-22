/- U-R C2 theta M-scale reading (kurt): corrected normalization of the lambda theta side.

Finding (Lead/david unit audit): actualRootCoeff = qVFamNormalizedCoefficient/(2l) and
qVFamNormalizedCoefficient = (qVFamily b).order = ord_P(q) at the selected F-place P = lift b, so
the current K-side theta hull log uses ord_P (not ord_b). The paper M-scale needs ord_b, hence a
factor 1/e_P (P | b). d_mod sits in the denominator already (Lead ruling 2026-11-17).

This file introduces the M-scale theta reading as a NEW definition (the DONE KSide definitions are
not modified):
  thetaMWeight (D) b := 1 / (lamWeight_b * eFiber_b)
  ksThetaHullLogRoot_lam_M (D) := sum_b thetaMWeight_b * thetaLamWeight_b * ksThetaHullLog_b
With eFiber_b = e_{P|b} and lamWeight_b = e_b*f_b the weight factor cancels and each term becomes
-ord_b/(2l*[Fmod:Q])*logp = -MpaperB_b (the scale identity is an EXPLICIT obligation of
ThetaMScaleData; the concrete eFiber is supplied by david's normalization audit).

Default heartbeats.
-/
import tmp.sheaf.xif.paper.Mzk1URThetaKSideActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators Pointwise

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaKLambdaMScaledActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULKSideLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open MeasureTheory

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (ksBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (ksBlock T b)]

/-- M-scale normalization data: the F-fibre ramification factor e_{P|b} (explicit obligation of
the theta M-scale correction; supplied by the normalization audit). -/
structure ThetaMScaleData where
  /-- e_{P|b} for the selected F-place P over b -/
  eFiber : Bad (nativePlaceSelection T) → ℝ
  /-- it is positive -/
  eFiber_pos : ∀ b, 0 < eFiber b

/-- The M-scale per-b weight: 1/(lambda_b * eFiber_b). -/
noncomputable def thetaMWeight (D : ThetaMScaleData (T := T)) (b : Bad (nativePlaceSelection T)) : ℝ :=
  1 / (lamWeight (l := l) T b * D.eFiber b)

/-- The M-scale lambda theta reading. -/
noncomputable def ksThetaHullLogRoot_lam_M (D : ThetaMScaleData (T := T)) : ℝ :=
  ∑ b : Bad (nativePlaceSelection T),
    thetaMWeight (l := l) T D b * thetaLamWeight (l := l) T b * ksThetaHullLog (l := l) T b

/-- Definitional reduction of the M-scale theta reading. -/
set_option maxHeartbeats 1000000 in
theorem ksThetaHullLogRoot_lam_M_scale (D : ThetaMScaleData (T := T)) :
    ksThetaHullLogRoot_lam_M (l := l) T D =
      ∑ b : Bad (nativePlaceSelection T),
        thetaMWeight (l := l) T D b * thetaLamWeight (l := l) T b *
          ksThetaHullLog (l := l) T b := rfl

#print axioms ksThetaHullLogRoot_lam_M_scale

end LeanFormal.IUT.XiFPaper.Mzk1URThetaKLambdaMScaledActual
end