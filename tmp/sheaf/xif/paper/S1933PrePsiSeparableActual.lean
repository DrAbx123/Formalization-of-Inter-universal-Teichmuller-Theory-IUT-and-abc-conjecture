/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
-/
import tmp.sheaf.xif.paper.S1924ZeroCriterionActual

/-!
# S1933: separability of prePsi_n via the derivative/gcd certificate

The remaining input of the S1906 rank-two basis route is exactly
S1366GenericOddPrePsiSeparableInput (S1366): for every elliptic Weierstrass curve over a
characteristic-zero field and every odd nonzero n, the odd division polynomial
prePsi n is separable.

Tau Ceti proves this by counting: over an algebraically closed field [n] is n^2-to-one,
so the n^2 - 1 nonzero n-torsion points map two-to-one onto the (n^2-1)/2 roots of
prePsi n (see the vendored copy tmp/TauCetiDivisionPolynomialSeparable.lean, which uses
card_zsmul_fiber and separable_of_natDegree_le_card_roots).  That route is excluded here,
and it is not importable at this Mathlib pin anyway.

This file works the pure derivative/gcd/Squarefree route instead.

## What is proved here

* S1933_bezout_three: the explicit Bezout certificate

  12*(b2^2 - 8*b2*X - 32*b4 - 48*X^2) * Psi_3
    + (144*X^3 + 36*b2*X^2 + (168*b4 - 4*b2^2)*X + (108*b6 - 4*b2*b4)) * (Psi_3)'
    = -12 * Delta

  in F[X], for every Weierstrass curve over a characteristic-zero field.  This is the
  derivative/gcd input for n = 3, obtained by eliminating b8 with
  4*b8 = b2*b6 - b4^2; it is a polynomial identity with no division.

* S1933_prePsi_three_separable: prePsi 3 is separable for every elliptic Weierstrass
  curve over a characteristic-zero field.  This is the first nontrivial case |n| > 1 of
  the target in the tree, and it uses no detection, no torsion count and no Nat.card.

* S1933Certificate: the general certificate shape, a Bezout identity
  A * prePsi n + B * (prePsi n)' = C (c * Delta^k) over the universal curve
  Z[a1,a2,a3,a4,a6].  S1933separable_of_certificate shows that one such certificate for a
  given n gives separability of prePsi n on every elliptic curve over every
  characteristic-zero field.

* S1933ExactFirstMissing: the exact first missing input, namely S1933Certificate n for
  every odd nonzero n.  S1933generic_of_certificates shows it yields the S1366 input, and
  S1933S1906Separability / S1933S1906BasisGap show it closes the S1906 input.

* S1933Certificate_one, S1933Certificate_neg_one: the certificate is realisable at
  n = +-1, where prePsi n = +-1.

## Why the certificate form is the right one

Separability/Squarefree is not preserved by specialization: X^2 - t is squarefree over
Q(t) but specializes to X^2 at t = 0.  So a proof that the generic curve has separable
prePsi n would not give the target.  What is preserved by an arbitrary ring homomorphism
is a Bezout identity, a witness for IsCoprime, which is why the missing input is stated as
a certificate over the universal curve rather than as separability of the universal
prePsi n.  Concretely, S1933_bezout_three exhibits exactly such a certificate at n = 3,
with k = 1 and c = -12.

## The exact gap

For every odd n >= 3 one needs explicit (A, B, c, k) with
A * prePsi n + B * (prePsi n)' = C (c * Delta^k) over Z[a1..a6].
Equivalently, via Resultant(f, f') = lc(f) * Disc f and the Sylvester adjugate, the
discriminant of prePsi n must be a nonzero rational multiple of a power of Delta; the
weight count forces the exponent k = (n^2-1)(n^2-3)/24 when Disc (prePsi n) = c_n * Delta^k.
At n = 3 this is Disc (Psi_3) = -27 * Delta^2 in the (a1,...,a6) presentation, which is the
identity behind S1933_bezout_three.  Nothing in Mathlib v4.32.2 supplies these identities,
and they are not derivable from the three-term EDS recurrences alone: the recurrences are
uniform in b2,b4,b6,b8, while the identity must use Delta != 0 (at Delta = 0, e.g. on
y^2 = x^3, one has prePsi 3 = 3*X^4, which is not squarefree).

## Verification status

No sorry, no admit, no axiom, no opaque.  See the axiom footprint at the end.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1933PrePsiSeparableActual

open Polynomial WeierstrassCurve
open LeanFormal.IUT.XiFPaper.S1366PrePsiSeparabilityFix
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1906RankTwoTorsionActual
open LeanFormal.IUT.XiFPaper.S1924ZeroCriterionActual

variable {F : Type*} [Field F] [CharZero F]

/-! ## 1. The relation 4 * b8 = b2 * b6 - b4^2, and the derivative of Psi_3 -/

/-- b8 in terms of b2, b4, b6; this is WeierstrassCurve.b_relation solved for b8.  It is the
only relation between the four b-invariants, and it is what lets the n = 3 certificate be
written with no division by b8. -/
theorem S1933_b8 (W : WeierstrassCurve F) : W.b₈ = (W.b₂ * W.b₆ - W.b₄ ^ 2) / 4 := by
  have h4 : (4 : F) ≠ 0 := by norm_num
  rw [eq_div_iff h4]
  linear_combination W.b_relation

/-- The derivative of the 3-division polynomial. -/
theorem S1933_derivative_Ψ₃ (W : WeierstrassCurve F) :
    derivative W.Ψ₃ = 12 * X ^ 3 + 3 * C W.b₂ * X ^ 2 + 6 * C W.b₄ * X + 3 * C W.b₆ := by
  simp only [WeierstrassCurve.Ψ₃]
  simp only [derivative_add, derivative_mul, derivative_C, derivative_X, derivative_pow,
    derivative_ofNat, derivative_natCast, derivative_C_mul_X_pow, derivative_X_pow]
  simp only [C_eq_natCast]
  ring

/-! ## 2. The n = 3 certificate and separability of prePsi 3 -/

/-- **The derivative/gcd certificate at n = 3.**  Explicit Bezout coefficients
A = 12*(b2^2 - 8*b2*X - 32*b4 - 48*X^2) and
B = 144*X^3 + 36*b2*X^2 + (168*b4 - 4*b2^2)*X + (108*b6 - 4*b2*b4)
satisfy A * Psi_3 + B * (Psi_3)' = -12 * Delta.  Both sides are polynomials over any
characteristic-zero field; the identity is checked after evaluating at a generic point, which
is legitimate because a characteristic-zero field is infinite. -/
theorem S1933_bezout_three (W : WeierstrassCurve F) :
    (12 * (C W.b₂ ^ 2 - 8 * C W.b₂ * X - 32 * C W.b₄ - 48 * X ^ 2)) * W.Ψ₃ +
      (144 * X ^ 3 + 36 * C W.b₂ * X ^ 2 + (168 * C W.b₄ - 4 * C W.b₂ ^ 2) * X +
        (108 * C W.b₆ - 4 * C W.b₂ * C W.b₄)) * derivative W.Ψ₃ =
      C (-12 * W.Δ) := by
  rw [S1933_derivative_Ψ₃]
  refine Polynomial.funext fun t => ?_
  simp only [WeierstrassCurve.Ψ₃, WeierstrassCurve.Δ]
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_sub, eval_neg, eval_ofNat,
    eval_natCast, eval_intCast, eval_one, eval_zero]
  rw [S1933_b8 W]
  field_simp
  ring

/-- **prePsi 3 is separable** for every elliptic Weierstrass curve over a characteristic-zero
field.  No detection, no torsion count, no Nat.card: the Bezout certificate
S1933_bezout_three turns into a unit right-hand side after inverting -12 * Delta, and
Delta is a unit on an elliptic curve. -/
theorem S1933_preΨ_three_separable (W : WeierstrassCurve F) [W.IsElliptic] :
    (W.preΨ 3).Separable := by
  rw [WeierstrassCurve.preΨ_three, separable_def']
  have hΔ : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
  set u : F := -12 * W.Δ with hu_def
  have hu : u ≠ 0 := by rw [hu_def]; exact mul_ne_zero (by norm_num) hΔ
  set A : F[X] := 12 * (C W.b₂ ^ 2 - 8 * C W.b₂ * X - 32 * C W.b₄ - 48 * X ^ 2) with hA
  set B : F[X] := 144 * X ^ 3 + 36 * C W.b₂ * X ^ 2 + (168 * C W.b₄ - 4 * C W.b₂ ^ 2) * X +
    (108 * C W.b₆ - 4 * C W.b₂ * C W.b₄) with hB
  have hcert : A * W.Ψ₃ + B * derivative W.Ψ₃ = C u := by
    rw [hA, hB, hu_def]
    exact S1933_bezout_three W
  refine ⟨A * C u⁻¹, B * C u⁻¹, ?_⟩
  have hC : C u * C u⁻¹ = (1 : F[X]) := by
    rw [← C_mul, mul_inv_cancel₀ hu, C_1]
  calc A * C u⁻¹ * W.Ψ₃ + B * C u⁻¹ * derivative W.Ψ₃
      = (A * W.Ψ₃ + B * derivative W.Ψ₃) * C u⁻¹ := by ring
    _ = C u * C u⁻¹ := by rw [hcert]
    _ = 1 := hC

/-! ## 3. The general certificate and its transfer to every curve -/

/-- The universal Weierstrass curve over Z[a1,a2,a3,a4,a6]. -/
def S1933W : WeierstrassCurve (MvPolynomial (Fin 5) ℤ) :=
  ⟨MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, MvPolynomial.X 3, MvPolynomial.X 4⟩

/-- **The derivative/gcd certificate at a given n.**  Explicit universal polynomials A, B and
integers c, k with A * prePsi n + B * (prePsi n)' = C (c * Delta^k) over the universal curve.
At n = 3 the corresponding identity is S1933_bezout_three, with c = -12 and k = 1; written in
the b-invariants it is a polynomial identity, so the universal certificate at n = 3 exists as
well, but that universal form is not formalised here. -/
def S1933Certificate (n : ℤ) : Prop :=
  ∃ (k : ℕ) (c : ℤ) (A B : (MvPolynomial (Fin 5) ℤ)[X]),
    c ≠ 0 ∧ A * S1933W.preΨ n + B * derivative (S1933W.preΨ n) =
      Polynomial.C (MvPolynomial.C c * S1933W.Δ ^ k)

/-- **A certificate at n gives separability of prePsi n on every curve.**  The certificate is
mapped along the specialization homomorphism Z[a1..a6] -> F determined by the coefficients of
the curve; a Bezout identity is preserved by ring homomorphisms (unlike Squarefree), and
Delta is a unit on an elliptic curve, so the right-hand side stays a unit. -/
theorem S1933separable_of_certificate (W : WeierstrassCurve F) [W.IsElliptic] {n : ℤ}
    (h : S1933Certificate n) : (W.preΨ n).Separable := by
  classical
  obtain ⟨k, c, A, B, hc, hAB⟩ := h
  have hcF : (c : F) ≠ 0 := by exact_mod_cast hc
  have hΔ : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
  set v : Fin 5 → F := ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆] with hv
  set φ : MvPolynomial (Fin 5) ℤ →+* F := MvPolynomial.eval₂Hom (Int.castRingHom F) v with hφ
  have hW : S1933W.map φ = W := by
    ext <;> simp [S1933W, hφ, hv]
  have hΔmap : φ S1933W.Δ = W.Δ := by
    rw [← WeierstrassCurve.map_Δ (W := S1933W) (f := φ), hW]
  have hcphi : φ (MvPolynomial.C c) = (c : F) := by
    rw [hφ, MvPolynomial.eval₂Hom_C]
    rfl
  have hm := congrArg (Polynomial.map φ) hAB
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map,
    ← WeierstrassCurve.map_preΨ, hW, Polynomial.map_C, map_mul, map_pow, hcphi, hΔmap] at hm
  rw [separable_def']
  refine ⟨A.map φ * C (((c : F) * W.Δ ^ k)⁻¹),
    B.map φ * C (((c : F) * W.Δ ^ k)⁻¹), ?_⟩
  have hu : ((c : F) * W.Δ ^ k) ≠ 0 := mul_ne_zero hcF (pow_ne_zero k hΔ)
  have hC : C ((c : F) * W.Δ ^ k) * C (((c : F) * W.Δ ^ k)⁻¹) = (1 : F[X]) := by
    rw [← C_mul, mul_inv_cancel₀ hu, C_1]
  calc A.map φ * C (((c : F) * W.Δ ^ k)⁻¹) * W.preΨ n +
        B.map φ * C (((c : F) * W.Δ ^ k)⁻¹) * derivative (W.preΨ n)
      = (A.map φ * W.preΨ n + B.map φ * derivative (W.preΨ n)) *
          C (((c : F) * W.Δ ^ k)⁻¹) := by ring
    _ = C ((c : F) * W.Δ ^ k) * C (((c : F) * W.Δ ^ k)⁻¹) := by rw [hm]
    _ = 1 := hC

/-! ## 4. The exact first missing input, its instances, and the consumers -/

/-- **The exact first missing input**: the derivative/gcd certificate at every odd nonzero n.
It is weaker than separability in the sense that it is a finite polynomial identity over the
universal curve, with no quantification over fields; by S1933separable_of_certificate it
implies the target. -/
def S1933ExactFirstMissing : Prop := ∀ n : ℤ, ¬ Even n → n ≠ 0 → S1933Certificate n

/-- The certificate at n = 1, where prePsi 1 = 1. -/
theorem S1933Certificate_one : S1933Certificate 1 := by
  refine ⟨0, 1, 1, 0, by norm_num, ?_⟩
  simp

/-- The certificate at n = -1, where prePsi (-1) = -1. -/
theorem S1933Certificate_neg_one : S1933Certificate (-1) := by
  refine ⟨0, -1, 1, 0, by norm_num, ?_⟩
  simp

/-- **The certificates give the S1366 generic separability input**, hence the S1906 input. -/
theorem S1933generic_of_certificates (h : S1933ExactFirstMissing) :
    S1366GenericOddPreΨSeparableInput := by
  intro F _ _ W _ n hodd hn
  exact S1933separable_of_certificate W (h n hodd hn)

/-- The certificates give separability of the actual prePsi_l of S1906. -/
theorem S1933S1906Separability (h : S1933ExactFirstMissing) (l : PrimeGeFive) :
    S1906Separability l :=
  S1933generic_of_certificates h S1906K S1906W (l.value : ℤ) (S1906_not_even l)
    (by exact_mod_cast l.prime.ne_zero)

/-- The certificates close the S1906 rank-two basis gap for every prime l >= 5. -/
theorem S1933S1906BasisGap (h : S1933ExactFirstMissing) (l : PrimeGeFive) :
    S1725RankTwoBasisGap l :=
  S1924S1906BasisGap_of_genericSeparable (S1933generic_of_certificates h) l

/-! ## 5. Axiom footprint -/

#print axioms S1933_b8
#print axioms S1933_derivative_Ψ₃
#print axioms S1933_bezout_three
#print axioms S1933_preΨ_three_separable
#print axioms S1933separable_of_certificate
#print axioms S1933Certificate_one
#print axioms S1933Certificate_neg_one
#print axioms S1933generic_of_certificates
#print axioms S1933S1906Separability
#print axioms S1933S1906BasisGap




end LeanFormal.IUT.XiFPaper.S1933PrePsiSeparableActual
