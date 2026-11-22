/-
Copyright (c) 2026 The IUT/ABC formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT/ABC formalization project
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence

/-!
# Bivariate division polynomials psi_n and omega_n, with point-evaluation laws

Mathlib v4.32.2 provides the bivariate division polynomials psi_n, phi_n and their
univariate companions, but it does not define the bivariate omega_n.  Its own module
docstring records the missing declaration as a TODO.  This file ports exactly the
definitional and point-evaluation part of the TauCeti development:

* the auxiliary second-complement summand complEDS2Aux;
* the six-way reduced invariant denominator reducedInvarDenom (definition only);
* the complement psi_c and the omega family, with the equation lemma omega_def;
* the basic values psi_c 0, psi_c 1, psi_c 2, omega 0, omega 1;
* the complement identity psi n * psi_c n = psi (2 * n);
* naturality of psi_c and omega in the coefficient ring;
* the point-evaluation laws evalEval_psi and evalEval_omega, and the complement
  companion evalEval_psi_c, against a minimal universal curve.

The universal curve below is only the slice needed to state the evaluation laws:
the five coefficient indeterminates, the specialisation homomorphism, and the
affine-plane evaluation homomorphism polyEval.  It is not the full TauCeti
universal-curve development (no coordinate ring, no pointed curve, no cusp model,
no Jacobian calculus).

## What is deliberately not ported

The defining identity

  2 * omega n + a1 * phi n * psi n + a3 * psi n ^ 3 = psi_c n

is not proved here.  In TauCeti it follows from the reduced-invariant identity
reducedInvarNum = reducedInvarDenom * (d + b ^ 4), whose proof needs
IsEllipticNet.invarNum/invarDenom theory and, in particular,
IsEllipticNet.normEDS.  That net theorem is an explicit TODO in Mathlib v4.32.2,
so the closure of the identity is not available in this workspace.  Nor are
omega_neg, baseChange_omega or the cusp evaluations ported, for the same reason.
The present file is the definition-and-point-evaluation slice requested for the
S1410 task; it makes no claim about the defining identity.

## Provenance

Adapted from TauCeti's
TauCeti/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Omega.lean and
TauCeti/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Universal.lean
(Apache-2.0).  The definitions complEDS2Aux and reducedInvarDenom are the
definitions from TauCeti/NumberTheory/EllipticDivisibilitySequence/ComplAux.lean
and ReducedInvariant.lean; only the definitions, not the surrounding invariant
theory, are vendored.  The upstream AINTLIB source credits J. Xu and
D. K. Angdinata; this file merely transports the relevant declarations to the
Mathlib v4.32.2 API.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

/-- The subtracted summand of Mathlib's complEDS2. -/
def complEDS₂Aux (b c d : R) (m : ℤ) : R :=
  preNormEDS (b ^ 4) c d (m - 2) * preNormEDS (b ^ 4) c d (m + 1) ^ 2 *
    if Even m then 1 else b

theorem complEDS₂Aux_def (b c d : R) (m : ℤ) :
    complEDS₂Aux b c d m =
      preNormEDS (b ^ 4) c d (m - 2) * preNormEDS (b ^ 4) c d (m + 1) ^ 2 *
        if Even m then 1 else b := rfl

@[simp]
theorem complEDS₂Aux_zero (b c d : R) : complEDS₂Aux b c d 0 = -1 := by
  simp [complEDS₂Aux_def]

@[simp]
theorem complEDS₂Aux_one (b c d : R) : complEDS₂Aux b c d 1 = -b := by
  simp [complEDS₂Aux_def]

@[simp]
theorem complEDS₂Aux_two (b c d : R) : complEDS₂Aux b c d 2 = 0 := by
  simp [complEDS₂Aux_def]

theorem map_complEDS₂Aux {S : Type*} [CommRing S] (f : R →+* S) (b c d : R) (m : ℤ) :
    f (complEDS₂Aux b c d m) = complEDS₂Aux (f b) (f c) (f d) m := by
  simp [complEDS₂Aux_def, apply_ite f]

/-- The reduced invariant denominator of a normalised EDS. -/
def reducedInvarDenom (b c d : R) (m : ℤ) : R :=
  let C := complEDS b c d
  let W := normEDS b c d
  let r₆ := W 5 - d ^ 2
  if m % 6 = 0 then r₆ * C 6 (m / 6) * W (m + 1) * W (m - 1)
  else if m % 6 = 1 then r₆ * C 6 ((m - 1) / 6) * W (m + 1) * W m
  else if m % 6 = 5 then r₆ * C 6 ((m + 1) / 6) * W m * W (m - 1)
  else if m % 6 = 2 then C 3 ((m + 1) / 3) * C 2 (m / 2) * W (m - 1)
  else if m % 6 = 4 then C 3 ((m - 1) / 3) * C 2 (m / 2) * W (m + 1)
  else C 3 (m / 3) * C 2 ((m - 1) / 2) * W (m + 1)

theorem reducedInvarDenom_def (b c d : R) (m : ℤ) :
    reducedInvarDenom b c d m =
      if m % 6 = 0 then
        (normEDS b c d 5 - d ^ 2) * complEDS b c d 6 (m / 6) *
          normEDS b c d (m + 1) * normEDS b c d (m - 1)
      else if m % 6 = 1 then
        (normEDS b c d 5 - d ^ 2) * complEDS b c d 6 ((m - 1) / 6) *
          normEDS b c d (m + 1) * normEDS b c d m
      else if m % 6 = 5 then
        (normEDS b c d 5 - d ^ 2) * complEDS b c d 6 ((m + 1) / 6) *
          normEDS b c d m * normEDS b c d (m - 1)
      else if m % 6 = 2 then
        complEDS b c d 3 ((m + 1) / 3) * complEDS b c d 2 (m / 2) * normEDS b c d (m - 1)
      else if m % 6 = 4 then
        complEDS b c d 3 ((m - 1) / 3) * complEDS b c d 2 (m / 2) * normEDS b c d (m + 1)
      else
        complEDS b c d 3 (m / 3) * complEDS b c d 2 ((m - 1) / 2) * normEDS b c d (m + 1) := rfl

@[simp]
theorem reducedInvarDenom_zero (b c d : R) : reducedInvarDenom b c d 0 = 0 := by
  rw [reducedInvarDenom_def]
  simp

@[simp]
theorem reducedInvarDenom_one (b c d : R) : reducedInvarDenom b c d 1 = 0 := by
  rw [reducedInvarDenom_def]
  simp

@[simp]
theorem reducedInvarDenom_two (b c d : R) : reducedInvarDenom b c d 2 = 1 := by
  rw [reducedInvarDenom_def]
  simp

theorem map_reducedInvarDenom {S : Type*} [CommRing S] (f : R →+* S) (b c d : R) (m : ℤ) :
    f (reducedInvarDenom b c d m) = reducedInvarDenom (f b) (f c) (f d) m := by
  rw [reducedInvarDenom_def, reducedInvarDenom_def]
  simp only [reducedInvarDenom_def, apply_ite f, map_mul, map_sub, map_pow, map_complEDS,
    map_normEDS, map_one, map_ofNat]

section PsiC

variable (W : WeierstrassCurve R)

/-- The complement of psi n in psi (2 n): the parameter-level second complement of the
division-polynomial EDS. -/
protected def ψc : ℤ → R[X][Y] := complEDS₂ W.ψ₂ (C W.Ψ₃) (C W.preΨ₄)

/-- Defining formula for psi_c.  The body is exposed, but consumers should rewrite through
this equation lemma rather than unfolding the protected definition. -/
theorem ψc_def : W.ψc = complEDS₂ W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) := rfl

@[simp]
theorem ψc_zero : W.ψc 0 = 2 := by rw [ψc_def, complEDS₂_zero]

@[simp]
theorem ψc_one : W.ψc 1 = W.ψ₂ := by rw [ψc_def, complEDS₂_one]

@[simp]
theorem ψc_two : W.ψc 2 = C W.preΨ₄ := by rw [ψc_def, complEDS₂_two]

/-- The complement identity: psi n * psi_c n = psi (2 * n). -/
theorem ψ_mul_ψc (n : ℤ) : W.ψ n * W.ψc n = W.ψ (2 * n) := by
  rw [ψc_def]
  change normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n *
    complEDS₂ W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n =
    normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) (2 * n)
  exact normEDS_mul_complEDS₂ ..

@[simp]
theorem ψc_neg (n : ℤ) : W.ψc (-n) = W.ψc n := by
  simp only [ψc_def, complEDS₂_neg]

/-- psi_c is natural in the coefficient ring. -/
theorem map_ψc {S : Type*} [CommRing S] (f : R →+* S) (n : ℤ) :
    (W.map f).ψc n = (W.ψc n).map (mapRingHom f) := by
  simp_rw [ψc_def, ← coe_mapRingHom, map_complEDS₂, map_ψ₂, map_Ψ₃, map_preΨ₄]
  simp

end PsiC

section Omega

variable (W : WeierstrassCurve R)

/-- The omega family of division polynomials.  Its defining formula is the ported
TauCeti definition; the defining identity two_mul_omega is not proved in this file
(see the module docstring). -/
protected def ω (n : ℤ) : R[X][Y] :=
  reducedInvarDenom W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n *
    ((CC W.a₁ * W.toAffine.polynomialY - W.toAffine.polynomialX) * C W.Ψ₃
      + 4 * W.toAffine.polynomial * (2 * W.toAffine.polynomial + C W.Ψ₂Sq))
  - complEDS₂Aux W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n + W.toAffine.negPolynomial * W.ψ n ^ 3

/-- Defining formula for omega.  Deliberately not a simp lemma, as in TauCeti. -/
theorem ω_def (n : ℤ) : W.ω n =
    reducedInvarDenom W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n *
      ((CC W.a₁ * W.toAffine.polynomialY - W.toAffine.polynomialX) * C W.Ψ₃
        + 4 * W.toAffine.polynomial * (2 * W.toAffine.polynomial + C W.Ψ₂Sq))
    - complEDS₂Aux W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n + W.toAffine.negPolynomial * W.ψ n ^ 3 := rfl

@[simp]
theorem ω_zero : W.ω 0 = 1 := by
  rw [ω_def, reducedInvarDenom_zero, complEDS₂Aux_zero, ψ_zero]
  ring

@[simp]
theorem ω_one : W.ω 1 = Y := by
  rw [ω_def, reducedInvarDenom_one, complEDS₂Aux_one, ψ_one, ψ₂, ← Affine.Y_sub_polynomialY]
  ring1

/-- omega is natural in the coefficient ring. -/
theorem map_ω {S : Type*} [CommRing S] (f : R →+* S) (n : ℤ) :
    (W.map f).ω n = (W.ω n).map (mapRingHom f) := by
  simp_rw [ω_def, ← coe_mapRingHom, map_add, map_sub, map_mul, map_pow,
    map_reducedInvarDenom, map_complEDS₂Aux, Affine.map_polynomial, Affine.map_polynomialX,
    Affine.map_polynomialY, Affine.map_negPolynomial, map_ψ₂, map_Ψ₃, map_preΨ₄, map_Ψ₂Sq, map_ψ]
  simp

end Omega

section UniversalPointEval

namespace S1410Universal

/-- The five coefficient indices for the universal Weierstrass curve. -/
inductive Coeff : Type
  | A₁ : Coeff
  | A₂ : Coeff
  | A₃ : Coeff
  | A₄ : Coeff
  | A₆ : Coeff

open MvPolynomial (X) in
/-- The universal Weierstrass curve over Z[A1,...,A6]. -/
def curve : WeierstrassCurve (MvPolynomial Coeff ℤ) where
  a₁ := X .A₁
  a₂ := X .A₂
  a₃ := X .A₃
  a₄ := X .A₄
  a₆ := X .A₆

/-- The bivariate polynomial ring of the universal curve. -/
abbrev Poly : Type := (MvPolynomial Coeff ℤ)[X][Y]

/-- Specialisation of the universal coefficients along a curve W. -/
def specialize (W : WeierstrassCurve R) : MvPolynomial Coeff ℤ →+* R :=
  (MvPolynomial.aeval (Coeff.rec W.a₁ W.a₂ W.a₃ W.a₄ W.a₆)).toRingHom

open MvPolynomial (X) in
@[simp]
theorem specialize_X (W : WeierstrassCurve R) (i : Coeff) :
    specialize W (X i) = Coeff.rec W.a₁ W.a₂ W.a₃ W.a₄ W.a₆ i := by
  simp [specialize]

@[simp]
theorem map_specialize (W : WeierstrassCurve R) :
    curve.map (specialize W) = W := by
  ext <;> simp [curve, specialize]

/-- A point in the affine plane induces a homomorphism from the universal bivariate
polynomial ring to the coefficient ring. -/
def polyEval (W : WeierstrassCurve R) (x y : R) : Poly →+* R :=
  eval₂RingHom (eval₂RingHom (specialize W) x) y

open Polynomial in
@[simp]
theorem polyEval_apply (W : WeierstrassCurve R) (x y : R) (p : Poly) :
    polyEval W x y p = (p.map (mapRingHom (specialize W))).evalEval x y :=
  eval₂_eval₂RingHom_apply _ _ _ _

end S1410Universal

open S1410Universal in
/-- Point-evaluation law for the bivariate psi family. -/
theorem evalEval_ψ (W : WeierstrassCurve R) (x y : R) (n : ℤ) :
    (W.ψ n).evalEval x y = polyEval W x y (curve.ψ n) := by
  rw [polyEval_apply, ← map_ψ (W := curve) (f := specialize W) (n := n), map_specialize]

open S1410Universal in
/-- Point-evaluation law for the bivariate omega family. -/
theorem evalEval_ω (W : WeierstrassCurve R) (x y : R) (n : ℤ) :
    (W.ω n).evalEval x y = polyEval W x y (curve.ω n) := by
  rw [polyEval_apply, ← map_ω (W := curve) (f := specialize W) (n := n), map_specialize]

open S1410Universal in
/-- Point-evaluation law for the complement psi_c. -/
theorem evalEval_ψc (W : WeierstrassCurve R) (x y : R) (n : ℤ) :
    (W.ψc n).evalEval x y = polyEval W x y (curve.ψc n) := by
  rw [polyEval_apply, ← map_ψc (W := curve) (f := specialize W) (n := n), map_specialize]

end UniversalPointEval

end WeierstrassCurve
