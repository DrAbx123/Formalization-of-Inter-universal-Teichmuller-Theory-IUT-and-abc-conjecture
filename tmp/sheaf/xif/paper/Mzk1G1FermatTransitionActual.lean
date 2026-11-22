/- G1-B Fermat chart overlap localizations, actual (route §2.1 / A1 interface). -/
import tmp.sheaf.xif.paper.Mzk1G1FermatAffineChartActual
import tmp.sheaf.xif.paper.Mzk1G1FermatSecondChartActual
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatTransitionActual

/-- Polynomial model of the two affine coordinates. -/
abbrev Poly : Type := MvPolynomial (Fin 2) ℚ

/-- The actual affine chart ring A0 = k[x,y]/(x^n+y^n-1) (multivariate presentation). -/
abbrev AffineChartRing (n : ℕ) : Type := R n
/-- The actual infinity chart ring A∞ = k[r,s]/(1+s^n-r^n) (multivariate presentation). -/
abbrev InfinityChartRing (n : ℕ) : Type := R2 n

/-- The x coordinate in the affine chart. -/
def affineX (n : ℕ) : R n := Ideal.Quotient.mk _ (MvPolynomial.X 0)
/-- The y coordinate in the affine chart. -/
def affineY (n : ℕ) : R n := Ideal.Quotient.mk _ (MvPolynomial.X 1)
/-- The s coordinate on the infinity chart (X 0 of the second-chart presentation). -/
def infinityS (n : ℕ) : R2 n := Ideal.Quotient.mk _ (MvPolynomial.X 0)
/-- The r coordinate on the infinity chart (X 1 of the second-chart presentation). -/
def infinityR (n : ℕ) : R2 n := Ideal.Quotient.mk _ (MvPolynomial.X 1)

/-- The affine chart Fermat relation x^n+y^n-1 = 0 in coordinates. -/
theorem affineX_pow_add_affineY_pow_sub_one (n : ℕ) :
    affineX n ^ n + affineY n ^ n - 1 = 0 := by
  have hmem : fermatEquation n ∈ Ideal.span ({fermatEquation n} : Set Poly) :=
    Ideal.subset_span (by simp)
  have hmk : Ideal.Quotient.mk (Ideal.span ({fermatEquation n} : Set Poly))
      (fermatEquation n) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have hsub : affineX n ^ n + affineY n ^ n - 1 = 0 := by
    rw [affineX, affineY, ← map_one (Ideal.Quotient.mk _), ← map_pow, ← map_pow,
      ← map_add, ← map_sub]
    exact hmk
  exact hsub

/-- The infinity chart Fermat relation 1+s^n-r^n = 0 in coordinates. -/
theorem infinityS_pow_add_one_sub_infinityR_pow (n : ℕ) :
    1 + infinityS n ^ n - infinityR n ^ n = 0 := by
  have hmem : secondEquation n ∈ Ideal.span ({secondEquation n} : Set Poly) :=
    Ideal.subset_span (by simp)
  have hmk : Ideal.Quotient.mk (Ideal.span ({secondEquation n} : Set Poly))
      (secondEquation n) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have hsub : 1 + infinityS n ^ n - infinityR n ^ n = 0 := by
    rw [infinityS, infinityR, ← map_one (Ideal.Quotient.mk _), ← map_pow, ← map_pow,
      ← map_add, ← map_sub]
    exact hmk
  exact hsub

/-- Overlap of the two charts inside the affine chart: localize at x (D(x) in U0). -/
abbrev AffineOverlap (n : ℕ) : Type := Localization.Away (affineX n)
/-- Overlap of the two charts inside the infinity chart: localize at r (D(r) in U∞). -/
abbrev InfinityOverlap (n : ℕ) : Type := Localization.Away (infinityR n)

/-- Image of x in the affine overlap. -/
def overlapX (n : ℕ) : AffineOverlap n := algebraMap _ _ (affineX n)
/-- Image of y in the affine overlap. -/
def overlapY (n : ℕ) : AffineOverlap n := algebraMap _ _ (affineY n)
/-- The r coordinate on the affine overlap: r = x⁻¹ (A1). -/
noncomputable def overlapR (n : ℕ) : AffineOverlap n :=
  IsLocalization.Away.invSelf (affineX n)
/-- The s coordinate on the affine overlap: s = y/x (A1). -/
noncomputable def overlapS (n : ℕ) : AffineOverlap n :=
  overlapY n * IsLocalization.Away.invSelf (affineX n)

theorem isUnit_overlapX (n : ℕ) : IsUnit (overlapX n) :=
  IsLocalization.Away.algebraMap_isUnit (x := affineX n) (S := AffineOverlap n)

theorem overlapX_mul_overlapR (n : ℕ) : overlapX n * overlapR n = 1 :=
  IsLocalization.Away.mul_invSelf (x := affineX n) (S := AffineOverlap n)

theorem overlapX_pow_mul_overlapR_pow (n : ℕ) :
    overlapX n ^ n * overlapR n ^ n = 1 := by
  rw [← mul_pow, overlapX_mul_overlapR, one_pow]

/-- The infinity-chart relation 1+s^n-r^n = 0 holds on the affine overlap (A1 compatibility). -/
theorem one_add_overlapS_pow_sub_overlapR_pow (n : ℕ) :
    1 + overlapS n ^ n - overlapR n ^ n = 0 := by
  have hrel : overlapX n ^ n + overlapY n ^ n - 1 = 0 := by
    have h := affineX_pow_add_affineY_pow_sub_one n
    have h' := congrArg (algebraMap (R n) (AffineOverlap n)) h
    rw [map_sub, map_add, map_pow, map_pow, map_one, map_zero] at h'
    simpa [overlapX, overlapY] using h'
  have hmul := IsLocalization.Away.mul_invSelf (x := affineX n) (S := AffineOverlap n)
  have hxn : overlapX n ^ n * (IsLocalization.Away.invSelf (affineX n)) ^ n = 1 := by
    rw [← mul_pow, show overlapX n * IsLocalization.Away.invSelf (affineX n) = 1 from hmul,
      one_pow]
  have hmul' : overlapX n ^ n *
      (overlapY n ^ n * (IsLocalization.Away.invSelf (affineX n)) ^ n) = overlapY n ^ n := by
    rw [mul_comm (overlapY n ^ n) (IsLocalization.Away.invSelf (affineX n) ^ n),
      ← mul_assoc, hxn, one_mul]
  have key : overlapX n ^ n *
      (1 + (overlapY n * IsLocalization.Away.invSelf (affineX n)) ^ n -
        (IsLocalization.Away.invSelf (affineX n)) ^ n) = 0 := by
    rw [mul_pow, mul_sub, mul_add, mul_one, hmul', hxn]
    exact hrel
  have hmain : 1 + (overlapY n * IsLocalization.Away.invSelf (affineX n)) ^ n -
      (IsLocalization.Away.invSelf (affineX n)) ^ n = 0 := by
    have hxn' : overlapX n ^ n * (IsLocalization.Away.invSelf (affineX n)) ^ n = 1 := hxn
    calc
      1 + (overlapY n * IsLocalization.Away.invSelf (affineX n)) ^ n -
            (IsLocalization.Away.invSelf (affineX n)) ^ n
          = (overlapX n ^ n * (IsLocalization.Away.invSelf (affineX n)) ^ n) *
              (1 + (overlapY n * IsLocalization.Away.invSelf (affineX n)) ^ n -
                (IsLocalization.Away.invSelf (affineX n)) ^ n) := by
              rw [hxn', one_mul]
      _ = (IsLocalization.Away.invSelf (affineX n)) ^ n *
              (overlapX n ^ n *
                (1 + (overlapY n * IsLocalization.Away.invSelf (affineX n)) ^ n -
                  (IsLocalization.Away.invSelf (affineX n)) ^ n)) := by
              rw [mul_comm (overlapX n ^ n) ((IsLocalization.Away.invSelf (affineX n)) ^ n),
                mul_assoc]
      _ = 0 := by rw [key, mul_zero]
  simpa [overlapS, overlapR] using hmain

#print axioms affineX_pow_add_affineY_pow_sub_one
#print axioms infinityS_pow_add_one_sub_infinityR_pow
#print axioms one_add_overlapS_pow_sub_overlapR_pow
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatTransitionActual
