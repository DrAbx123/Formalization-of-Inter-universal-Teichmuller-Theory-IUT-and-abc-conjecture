/- R1: per-b reduction of hperB to ONE explicit coefficient-scale input (kurt).

Target (R1 single open): qPilotMass(cPFullFiber_b) <= thetaLamWeight_b * ksThetaHullLog_b.

PROVED here:
 * hperB_of_coeffScale_le (hcoef : thetaLamWeight_b * urCeilC_b <= cPFullFiber_b/(2l))
   (hlogp : 0 < log p) (hlam0 : 0 <= thetaLamWeight_b) :
     qPilotMass(cPFullFiber_b) <= thetaLamWeight_b * ksThetaHullLog_b.
Proof: DONE ceil lower bound ksThetaHullLog_lower : -(urCeilC log p) <= ksThetaHullLog; multiply by
thetaLamWeight >= 0; the coefficient-scale hypothesis turns -(thetaLamWeight*urCeilC*log p) into
an upper bound for qPilotMass.

DIRECTION NOTE (important): because ksThetaHullLog_lower is a LOWER bound on ksThetaHullLog, the
sufficient coefficient condition for hperB is
  thetaLamWeight_b * urCeilC_b <= cPFullFiber_b/(2l)
(i.e. <=, not >=).  With cPFullFiber_b = v_sel/d_mod and thetaLamWeight = lambda/d_mod,
urCeilC >= v_sel/(2l) this reads (lambda/d_mod)*urCeilC <= v_sel/(2 l d_mod), i.e.
lambda * urCeilC <= v_sel/(2l), which fails per b when lambda > 1: so the per-b form needs the
ceil-region to be replaced by the root lattice (qLatticeMass caliber) or a summation-level form.
No fake proof is added for the failing direction.
-/
import tmp.sheaf.xif.paper.Mzk1URThetaKLowerBoundActual
import tmp.sheaf.xif.paper.Mzk1URThetaKSideActual
import tmp.sheaf.xif.paper.Mzk1URRootNuOnePlaceActual
import tmp.sheaf.xif.paper.Mzk1ULR1MpaperBWeightActual
import tmp.sheaf.xif.paper.Mzk1URThetaHullInclusionActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaHperBReductionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1URRootNuOnePlaceActual
open LeanFormal.IUT.XiFPaper.Mzk1ULR1MpaperBWeightActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaHullInclusionActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Per-b hperB from the coefficient-scale condition (sufficient direction: <=). -/
theorem hperB_of_coeffScale_le (b : Bad (nativePlaceSelection T))
    (hlogp : 0 < Real.log (qVFamTensorP T b : ℝ))
    (hlam0 : 0 ≤ thetaLamWeight (l := l) T b)
    (hcoef : thetaLamWeight (l := l) T b * urCeilC (l := l) T b ≤
      cPFullFiber (l := l) T b / (2 * (l.value : ℝ))) :
    qPilotMass (T := T) (b := b) (cPFullFiber (l := l) T b) ≤
      thetaLamWeight (l := l) T b * ksThetaHullLog (l := l) T b := by
  have hvol := Mzk1URThetaKLowerBoundActual.ksThetaHullLog_lower (l := l) T b
  have hq : qPilotMass (T := T) (b := b) (cPFullFiber (l := l) T b) =
      -(cPFullFiber (l := l) T b / (2 * (l.value : ℝ))) *
        Real.log (qVFamTensorP T b : ℝ) :=
    qPilotMass_eq (T := T) (b := b) (cPFullFiber (l := l) T b)
  rw [hq]
  have h1 := mul_le_mul_of_nonneg_left hvol hlam0
  have h2 := mul_le_mul_of_nonneg_right hcoef (le_of_lt hlogp)
  nlinarith

#print axioms hperB_of_coeffScale_le


/-- The ceiling is at least the actual root coefficient (spectral caliber). -/
theorem urCeilC_ge_actualRootCoeff (b : Bad (nativePlaceSelection T)) :
    actualRootCoeff (l := l) T b () ≤ urCeilC (l := l) T b := by
  rw [urCeilC_eq (l := l) T b]
  unfold ksCeilCoeff
  apply Mzk1URThetaHullUpperActual.le_ceilExp
  unfold actualRootCoeff
  have hc : 0 ≤ qVFamNormalizedCoefficient T b :=
    QVFamNormalizedCoefficientActual.qVFamNormalizedCoefficient_nonneg (T := T) (b := b)
  positivity

/-- R0.2-reduced coefficient scale: thetaLamWeight * urCeilC >= cPFullFiber/(2l), from the
crosswalk cPFullFiber = (lambda/d_mod) * cP_local with cP_local = qVFamNormalizedCoefficient. -/
theorem hcoef_prime (b : Bad (nativePlaceSelection T))
    (hcross : cPFullFiber (l := l) T b =
      (lamWeight (l := l) T b / dModF (l := l) T) *
        QVFamNormalizedCoefficient T b) :
    thetaLamWeight (l := l) T b * urCeilC (l := l) T b ≥
      cPFullFiber (l := l) T b / (2 * (l.value : ℝ)) := by
  have hceil := urCeilC_ge_actualRootCoeff (l := l) T b
  have hlam0 : 0 ≤ thetaLamWeight (l := l) T b := thetaLamWeight_nonneg T b
  have hmul := mul_le_mul_of_nonneg_left hceil hlam0
  have hroot : actualRootCoeff (l := l) T b () =
      QVFamNormalizedCoefficient T b / (2 * (l.value : ℝ)) := rfl
  rw [hroot] at hmul
  have hkey : thetaLamWeight (l := l) T b *
        (QVFamNormalizedCoefficient T b / (2 * (l.value : ℝ))) =
      cPFullFiber (l := l) T b / (2 * (l.value : ℝ)) := by
    rw [hcross]
    unfold thetaLamWeight
    ring
  linarith

/-- NOTE: hperB is NOT claimed from the ceil lower bound here: the sufficient per-b condition is
the <= form thetaLamWeight*urCeilC <= cPFullFiber/(2l), while hcoef_prime gives >= ; the two
directions differ under the K-side ceiling (decision record, Lead 2026-11-18). The container/L_w
reformulation (root-lattice masses, qLatticeMass) is the correct R1 route.

#print axioms urCeilC_ge_actualRootCoeff
#print axioms hcoef_prime
#print axioms hperB_of_crosswalk

end LeanFormal.IUT.XiFPaper.Mzk1URThetaHperBReductionActual
end