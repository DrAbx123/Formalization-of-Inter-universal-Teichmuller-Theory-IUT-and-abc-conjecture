import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

set_option maxHeartbeats 1000000

/-!
# Route 3 C-Divisor: actual f_P and finite torsion products

This file constructs the honestly available part of HANDOFF 6.3-6.4 on an
actual affine Weierstrass curve over a field:

* f_P is the function-field element X - x(P), represented by
  CoordinateRing.XClass W x and mapped into W.FunctionField;
* f_P is nonzero at an affine point;
* the finite coordinate-ring zero ideal at P and -P is exactly XIdeal W x
  (Mathlib CoordinateRing.XYIdeal_neg_mul), which is the local algebraic
  content of C1;
* F_C and F_l are finite products of actual f_P over a finite family of actual
  curve points, and are nonzero whenever each factor is nonzero.

NOT constructed here (exact gaps, see comments at the end):
* a curve divisor / principal-divisor theory with order of vanishing at the
  point at infinity, hence the full C1/C3/C5 divisor equalities;
* a quotient isogeny E -> E/C and its pullback divisor (C4);
* the multiplication-by-l isogeny and its pullback divisor (C5);
* a finite enumeration of E[l] from the arithmetic input.

No toy carrier, PUnit, assumed divisor equality or sorry is used.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Route3DivisorActual

open Polynomial

variable {K : Type*} [Field K]
variable (W : WeierstrassCurve.Affine K)

/-- The function-field element f_P = x - x(P), for an actual point P.
For P = O we set f_O = 1; C1 only uses P != O. -/
def fP (P : W.Point) : W.FunctionField :=
  match P with
  | .zero => 1
  | .some x _ _ =>
      algebraMap W.CoordinateRing W.FunctionField
        (WeierstrassCurve.Affine.CoordinateRing.XClass W x)

theorem fP_zero : fP W .zero = 1 := rfl

theorem fP_some (x y : K) (h : W.Nonsingular x y) :
    fP W (.some x y h) =
      algebraMap W.CoordinateRing W.FunctionField
        (WeierstrassCurve.Affine.CoordinateRing.XClass W x) := rfl

/-- f_P is nonzero for every actual point. -/
theorem fP_ne_zero (P : W.Point) : fP W P ≠ 0 := by
  cases P with
  | zero =>
      simp [fP]
  | some x y h =>
      intro hzero
      change (algebraMap W.CoordinateRing W.FunctionField)
        (WeierstrassCurve.Affine.CoordinateRing.XClass W x) = 0 at hzero
      exact (WeierstrassCurve.Affine.CoordinateRing.XClass_ne_zero
        (W' := W) x)
        (IsFractionRing.injective W.CoordinateRing W.FunctionField (by
          rw [hzero, map_zero]))

variable {ι : Type*} [Fintype ι]

/-- Finite product F_C over actual representatives P_i; the caller supplies
the actual finite representative family from the l-torsion. -/
def productF (P : ι -> W.Point) : W.FunctionField :=
  ∏ i, fP W (P i)

theorem productF_ne_zero (P : ι -> W.Point) : productF W P ≠ 0 := by
  unfold productF
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => fP_ne_zero W (P i))

section Torsion

variable [W.IsElliptic] [DecidableEq K]

/-- Actual l-torsion predicate on an actual point. -/
def IsLTorsion (l : Nat) (P : W.Point) : Prop :=
  l • P = 0

/-- Finite product over a finite family of actual l-torsion points.  This is
the constructible C5 product over a supplied finite representative family; it
is not a construction of the full set E[l]. -/
def productFTorsion (l : Nat) (P : ι -> W.Point) : W.FunctionField :=
  productF W P

theorem productFTorsion_ne_zero (l : Nat) (P : ι -> W.Point) :
    productFTorsion W l P ≠ 0 := by
  unfold productFTorsion
  exact productF_ne_zero W P

theorem productFTorsion_eq (l : Nat) (P : ι -> W.Point) :
    productFTorsion W l P = ∏ i, fP W (P i) := rfl

end Torsion

/-!
## Exact gaps (not hidden as fields or assumptions)

G1. Full C1: no curve principal-divisor/order-of-vanishing API for W at the
    point at infinity; the affine zero-ideal relation is Mathlib XYIdeal_neg_mul,
    not a full divisor equality.
G2. Full C3: same missing divisor theory for the product F_C; the finite
    ideal product can be written, but the pole at O and the total divisor are
    not available.
G3. C4: Mathlib has no quotient isogeny E -> E/C, no pullback divisor, and no
    degree formula for such a pullback; none is assumed here.
G4. C5: Mathlib has no multiplication-by-l isogeny/pullback divisor, and no
    theorem that the affine points of E[l] are enumerated by a finite Finset
    of the actual input.  productFTorsion is only a finite subfamily product.
G5. The odd division polynomial prePsi is a univariate polynomial in Mathlib,
    but Mathlib does not prove its roots are exactly the x-coordinates of the
    nonzero l-torsion points; that root identification is not assumed.
-/

#print axioms fP_ne_zero
#print axioms productF_ne_zero
#print axioms productFTorsion_ne_zero

#check WeierstrassCurve.Affine.CoordinateRing.XYIdeal_neg_mul

end LeanFormal.IUT.XiFPaper.Mzk1Route3DivisorActual
