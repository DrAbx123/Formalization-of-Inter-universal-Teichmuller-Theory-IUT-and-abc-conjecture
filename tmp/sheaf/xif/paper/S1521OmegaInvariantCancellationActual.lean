/-
Copyright (c) 2026 The IUT/ABC formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT/ABC formalization project
-/
import tmp.sheaf.xif.paper.S1509OmegaDefiningIdentityActual
/-!
# S1521: the invariant cancellation of the normalised EDS

This file ports the invariant half of TauCeti's
TauCeti/NumberTheory/EllipticDivisibilitySequence/{Invariant/Basic,Invariant/NormEDS,
Complement,ComplAux,Six,ReducedInvariant}.lean on top of the S1491 net theorem
IsEllipticNet.normEDS.  It supplies

* the candidate numerator/denominator IsEllipticNet.invarNum/invarDenom and the
  cross-multiplication identity invarNum_mul_invarDenom;
* the two cancellation lemmas
  IsEllipticNet.invarNum_normEDS_one_eq_reducedInvarNum_mul and
  IsEllipticNet.invarDenom_normEDS_one_eq_reducedInvarDenom_mul;
* the reduced invariant identity
  reducedInvarNum_eq_reducedInvarDenom_mul.

The only extra ingredient Mathlib v4.32.2 lacks for the denominator cancellation is
normEDS_mul_complEDS, which is proved here by the same universal-specialisation and
complEDSRec argument as TauCeti's pinned Mathlib.

The omega defining identity and the division-polynomial polynomial identities are added
below once these cancellations are available.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
open Polynomial
open scoped Polynomial.Bivariate
open scoped nonZeroDivisors
namespace IsEllipticNet
section Numerator
variable {R S : Type*} [Add R] [Monoid R] [Add S] [Monoid S] (W : ℤ → R)
/-- The candidate numerator of the invariant of an arbitrary sequence. -/
def invarNum (s n : ℤ) : R :=
  (W (n + 2 * s) * W (n - s) ^ 2 + W (n + s) ^ 2 * W (n - 2 * s)) * W s ^ 2
    + W n ^ 3 * W (2 * s) ^ 2
@[simp]
theorem invarNum_def (s n : ℤ) : invarNum W s n =
    (W (n + 2 * s) * W (n - s) ^ 2 + W (n + s) ^ 2 * W (n - 2 * s)) * W s ^ 2
      + W n ^ 3 * W (2 * s) ^ 2 := rfl
theorem map_invarNum {F : Type*} [FunLike F R S]
    [AddHomClass F R S] [MonoidHomClass F R S] (f : F) (s n : ℤ) :
    f (invarNum W s n) = invarNum (f ∘ W) s n := by
  simp only [invarNum, map_add, map_mul, map_pow, Function.comp_apply]
end Numerator
section Denominator
variable {R S : Type*} [Mul R] [Mul S] (W : ℤ → R)
/-- The denominator of the invariant of an elliptic net. -/
def invarDenom (s n : ℤ) : R := W (n + s) * W n * W (n - s)
@[simp]
theorem invarDenom_def (s n : ℤ) : invarDenom W s n = W (n + s) * W n * W (n - s) := rfl
theorem map_invarDenom {F : Type*} [FunLike F R S] [MulHomClass F R S]
    (f : F) (s n : ℤ) :
    f (invarDenom W s n) = invarDenom (f ∘ W) s n := by
  simp only [invarDenom, map_mul, Function.comp_apply]
end Denominator
section CommRing
variable {R : Type*} [CommRing R] {W : ℤ → R}
private theorem invarNum_mul_invarDenom_of_rel {s m n : ℤ}
    (h₀ : rel W m n s 0 = 0) (h₁ : rel W m n s s = 0)
    (h₂ : rel W (m - s) (n - s) s s = 0) (h₃ : rel W (n + s) n (n - s) (m - n) = 0) :
    invarNum W s m * invarDenom W s n = invarNum W s n * invarDenom W s m := by
  simp_rw [invarNum, invarDenom]
  linear_combination (norm := (simp_rw [rel]; ring_nf))
    h₀ * W m * W n * W (2 * s) ^ 2
      - (h₁ * W (m - s) * W (n - s)
        + h₂ * W (m + s) * W (n + s)
        - h₃ * W (m - n) * W (2 * s)) * W s ^ 2
/-- **The invariance identity for an elliptic net**. -/
theorem invarNum_mul_invarDenom (h : IsEllipticNet W) (s m n : ℤ) :
    invarNum W s m * invarDenom W s n = invarNum W s n * invarDenom W s m :=
  invarNum_mul_invarDenom_of_rel (h ..) (h ..) (h ..) (h ..)
end CommRing
end IsEllipticNet
namespace WeierstrassCurve
variable {R : Type*} [CommRing R]
/-- The auxiliary term of the second complement times b. -/
theorem complEDS₂Aux_mul_b (b c d : R) (m : ℤ) :
    complEDS₂Aux b c d m * b = normEDS b c d (m - 2) * normEDS b c d (m + 1) ^ 2 := by
  simp_rw [complEDS₂Aux, normEDS, Int.even_add, Int.even_sub, even_two, Int.not_even_one,
    iff_true, iff_false]
  split_ifs <;> ring
/-- The sixth term of a normalised EDS. -/
theorem normEDS_six (b c d : R) :
    normEDS b c d 6 = (normEDS b c d 5 - d ^ 2) * b * c := by
  rw [show (6 : ℤ) = 2 * 3 by rfl, ← normEDS_mul_complEDS₂, complEDS₂_three, normEDS_three]
  norm_num [normEDS, Int.even_iff]
  ring
/-- The normalised EDS with parameters (2,3,2) is the identity sequence. -/
@[simp]
theorem normEDS_two_three_two (n : ℤ) : normEDS 2 3 2 n = n := by
  induction n using Int.negInduction with
  | nat n =>
    induction n using normEDSRec with
    | zero => norm_num
    | one => norm_num
    | two => norm_num
    | three => norm_num
    | four => norm_num
    | even m ih1 ih2 ih3 ih4 ih5 =>
      rw [show ((2 * (m + 3) : ℕ) : ℤ) = 2 * ((m : ℤ) + 3) by push_cast; ring]
      have h := normEDS_even (2 : ℤ) 3 2 ((m : ℤ) + 3)
      rw [show ((m : ℤ) + 3 - 1) = ((m + 2 : ℕ) : ℤ) by push_cast; ring,
        show ((m : ℤ) + 3 + 2) = ((m + 5 : ℕ) : ℤ) by push_cast; ring,
        show ((m : ℤ) + 3 - 2) = ((m + 1 : ℕ) : ℤ) by push_cast; ring,
        show ((m : ℤ) + 3 + 1) = ((m + 4 : ℕ) : ℤ) by push_cast; ring] at h
      rw [show (m : ℤ) + 3 = ((m + 3 : ℕ) : ℤ) by push_cast; ring] at h
      simp only [ih1, ih2, ih3, ih4, ih5] at h
      push_cast at h
      ring_nf at h ⊢
      omega
    | odd m ih1 ih2 ih3 ih4 =>
      rw [show ((2 * (m + 2) + 1 : ℕ) : ℤ) = 2 * ((m : ℤ) + 2) + 1 by push_cast; ring]
      have h := normEDS_odd (2 : ℤ) 3 2 ((m : ℤ) + 2)
      rw [show ((m : ℤ) + 2 - 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring,
        show ((m : ℤ) + 2 + 1) = ((m + 3 : ℕ) : ℤ) by push_cast; ring,
        show ((m : ℤ) + 2 + 2) = ((m + 4 : ℕ) : ℤ) by push_cast; ring] at h
      rw [show (m : ℤ) + 2 = ((m + 2 : ℕ) : ℤ) by push_cast; ring] at h
      simp only [ih1, ih2, ih3, ih4] at h
      push_cast at h
      ring_nf at h ⊢
      omega
  | neg ih n => rw [normEDS_neg, ih]
end WeierstrassCurve
namespace WeierstrassCurve
variable {R : Type*} [CommRing R]
open MvPolynomial in
/-- **The complement witnesses divisibility at every multiple.**  This is the theorem
normEDS_mul_complEDS of TauCeti's pinned Mathlib, absent from Mathlib v4.32.2. -/
theorem normEDS_mul_complEDS (b c d : R) (m n : ℤ) :
    normEDS b c d m * complEDS b c d m n = normEDS b c d (n * m) := by
  let N (m : ℤ) : MvPolynomial (Fin 3) ℤ := normEDS (X 0) (X 1) (X 2) m
  suffices hN : N m * complEDS (X 0) (X 1) (X 2) m n = N (n * m) by
    simpa [N] using congr(aeval ![b, c, d] $hN)
  by_cases hm : m = 0
  · simp [N, hm]
  induction n using Int.negInduction with
  | nat n => induction n using complEDSRec with
    | zero | one => simp [N]
    | even => rw [Nat.cast_mul, Nat.cast_ofNat, complEDS_even]; grind only [normEDS_mul_complEDS₂]
    | odd k ih₁ ih₂ =>
      apply mul_left_cancel₀ (a := N m) fun h ↦ hm <| by simpa [N] using congr(eval ![2, 3, 2] $h)
      grind [complEDS_odd _ _ _ m <| k + 1, normEDS_one, IsEllipticNet.rel,
        IsEllipticSequence.normEDS (@X ℤ _ _ (0 : Fin 3)) (X 1) (X 2) ((k + 2) * m) ((k + 1) * m) 1]
  | neg h n => simpa [N] using h n
/-- The complement at a divisor. -/
theorem normEDS_mul_complEDS_div (b c d : R) (k n : ℤ) (hn : k ∣ n) :
    normEDS b c d k * complEDS b c d k (n / k) = normEDS b c d n := by
  rw [normEDS_mul_complEDS, Int.ediv_mul_cancel hn]
end WeierstrassCurve
namespace WeierstrassCurve
variable {R : Type*} [CommRing R] (b c d : R) (m : ℤ)
theorem reducedInvarDenom_of_emod_six_eq_zero (h : m % 6 = 0) :
    reducedInvarDenom b c d m = (normEDS b c d 5 - d ^ 2) * complEDS b c d 6 (m / 6) *
      normEDS b c d (m + 1) * normEDS b c d (m - 1) := by
  simp [reducedInvarDenom_def, h]
theorem reducedInvarDenom_of_emod_six_eq_one (h : m % 6 = 1) :
    reducedInvarDenom b c d m = (normEDS b c d 5 - d ^ 2) * complEDS b c d 6 ((m - 1) / 6) *
      normEDS b c d (m + 1) * normEDS b c d m := by
  simp [reducedInvarDenom_def, h]
theorem reducedInvarDenom_of_emod_six_eq_five (h : m % 6 = 5) :
    reducedInvarDenom b c d m = (normEDS b c d 5 - d ^ 2) * complEDS b c d 6 ((m + 1) / 6) *
      normEDS b c d m * normEDS b c d (m - 1) := by
  simp [reducedInvarDenom_def, h]
theorem reducedInvarDenom_of_emod_six_eq_two (h : m % 6 = 2) :
    reducedInvarDenom b c d m =
      complEDS b c d 3 ((m + 1) / 3) * complEDS b c d 2 (m / 2) * normEDS b c d (m - 1) := by
  simp [reducedInvarDenom_def, h]
theorem reducedInvarDenom_of_emod_six_eq_four (h : m % 6 = 4) :
    reducedInvarDenom b c d m =
      complEDS b c d 3 ((m - 1) / 3) * complEDS b c d 2 (m / 2) * normEDS b c d (m + 1) := by
  simp [reducedInvarDenom_def, h]
theorem reducedInvarDenom_of_emod_six_eq_three (h : m % 6 = 3) :
    reducedInvarDenom b c d m =
      complEDS b c d 3 (m / 3) * complEDS b c d 2 ((m - 1) / 2) * normEDS b c d (m + 1) := by
  simp [reducedInvarDenom_def, h]
end WeierstrassCurve
namespace IsEllipticNet
variable {R : Type*} [CommRing R] {b c d : R}
open MvPolynomial
theorem invarNum_normEDS_one_two (b c d : R) :
    invarNum (_root_.normEDS b c d) 1 2 = (d + b ^ 4) * b := by
  simp only [invarNum_def, mul_one, Int.reduceAdd, normEDS_four, Int.reduceSub, normEDS_one,
    one_pow, normEDS_three, sub_self, normEDS_zero, mul_zero, add_zero, normEDS_two]
  ring
theorem invarDenom_normEDS_one_two (b c d : R) :
    invarDenom (_root_.normEDS b c d) 1 2 = c * b := by
  simp
private theorem invarNum_normEDS_one_mul_eq_invarDenom_mul_of_mem (hb : b ∈ R⁰) (m : ℤ) :
    invarNum (_root_.normEDS b c d) 1 m * c =
      invarDenom (_root_.normEDS b c d) 1 m * (d + b ^ 4) := by
  rw [← mul_cancel_right_mem_nonZeroDivisors hb]
  have h := invarNum_mul_invarDenom (IsEllipticNet.normEDS b c d) 1 m 2
  rw [invarNum_normEDS_one_two, invarDenom_normEDS_one_two] at h
  linear_combination h
end IsEllipticNet
inductive NormEDSParam : Type | B : NormEDSParam | C : NormEDSParam | D : NormEDSParam
namespace NormEDSParam
open MvPolynomial
variable {R : Type*} [CommRing R] (b c d : R)
noncomputable def universalNormEDS : ℤ → MvPolynomial NormEDSParam ℤ :=
  normEDS (X B) (X C) (X D)
@[simp]
theorem universalNormEDS_def :
    (universalNormEDS : ℤ → MvPolynomial NormEDSParam ℤ) =
      normEDS (X NormEDSParam.B) (X NormEDSParam.C) (X NormEDSParam.D) := rfl
theorem normEDS_eq_aeval :
    normEDS b c d = fun n => aeval (NormEDSParam.rec b c d) (universalNormEDS n) := by
  simp_rw [universalNormEDS, map_normEDS, MvPolynomial.aeval_X]
end NormEDSParam
namespace IsEllipticNet
open MvPolynomial NormEDSParam
variable {R : Type*} [CommRing R] {b c d : R}
theorem invarNum_normEDS_one_mul_eq_invarDenom_mul (b c d : R) (m : ℤ) :
    invarNum (_root_.normEDS b c d) 1 m * c =
      invarDenom (_root_.normEDS b c d) 1 m * (d + b ^ 4) := by
  have huniv := invarNum_normEDS_one_mul_eq_invarDenom_mul_of_mem
    (b := (X B : MvPolynomial NormEDSParam ℤ)) (c := X C) (d := X D)
    (mem_nonZeroDivisors_of_ne_zero (X_ne_zero (R := ℤ) B)) m
  have key := congr(aeval (NormEDSParam.rec b c d) $huniv)
  rw [NormEDSParam.normEDS_eq_aeval (b := b) (c := c) (d := d), ← Function.comp_def,
    ← map_invarNum, ← map_invarDenom, NormEDSParam.universalNormEDS_def]
  simpa only [map_mul, map_add, map_pow, MvPolynomial.aeval_X] using key
end IsEllipticNet
namespace WeierstrassCurve
variable {R S : Type*} [CommRing R] [CommRing S] (b c d : R) (m : ℤ)
theorem map_complEDS₂Aux' {F : Type*} [FunLike F R S] [RingHomClass F R S] (f : F) :
    f (complEDS₂Aux b c d m) = complEDS₂Aux (f b) (f c) (f d) m := by
  simp [complEDS₂Aux_def, apply_ite f]
@[simp]
theorem map_reducedInvarNum {F : Type*} [FunLike F R S] [RingHomClass F R S] (f : F) :
    f (reducedInvarNum b c d m) = reducedInvarNum (f b) (f c) (f d) m := by
  simp [reducedInvarNum_def, map_complEDS₂Aux', map_ofNat]
/-- Generic-ring-hom naturality of reducedInvarDenom, parallel to S1410's ring-hom form. -/
theorem map_reducedInvarDenom' {F : Type*} [FunLike F R S] [RingHomClass F R S] (f : F) :
    f (reducedInvarDenom b c d m) = reducedInvarDenom (f b) (f c) (f d) m := by
  rw [reducedInvarDenom_def, reducedInvarDenom_def]
  simp only [apply_ite f, map_mul, map_sub, map_pow, map_complEDS, map_normEDS]
end WeierstrassCurve
namespace IsEllipticNet
open WeierstrassCurve
variable {R : Type*} [CommRing R] {b c d : R}
/-- **The cancellation reducedInvarDenom is named for**: the invariant denominator at s = 1
is reducedInvarDenom times b * c, unconditionally over any commutative ring. -/
@[simp high]
theorem invarDenom_normEDS_one_eq_reducedInvarDenom_mul (b c d : R) (m : ℤ) :
    invarDenom (_root_.normEDS b c d) 1 m = reducedInvarDenom b c d m * (b * c) := by
  have h6 : ∀ k : ℤ, (6 : ℤ) ∣ k →
      _root_.normEDS b c d k =
        (_root_.normEDS b c d 5 - d ^ 2) * complEDS b c d 6 (k / 6) * (b * c) :=
    fun k h => by
      rw [← WeierstrassCurve.normEDS_mul_complEDS_div b c d 6 k h, WeierstrassCurve.normEDS_six]
      ring
  have h3 : ∀ k : ℤ, (3 : ℤ) ∣ k →
      _root_.normEDS b c d k = complEDS b c d 3 (k / 3) * c :=
    fun k h => by
      rw [← WeierstrassCurve.normEDS_mul_complEDS_div b c d 3 k h, normEDS_three]
      ring
  have h2 : ∀ k : ℤ, (2 : ℤ) ∣ k →
      _root_.normEDS b c d k = complEDS b c d 2 (k / 2) * b :=
    fun k h => by
      rw [← WeierstrassCurve.normEDS_mul_complEDS_div b c d 2 k h, normEDS_two]
      ring
  have hcase : m % 6 = 0 ∨ m % 6 = 1 ∨ m % 6 = 2 ∨ m % 6 = 3 ∨ m % 6 = 4 ∨ m % 6 = 5 := by
    omega
  rw [invarDenom_def]
  rcases hcase with h | h | h | h | h | h
  · rw [reducedInvarDenom_of_emod_six_eq_zero b c d m h, h6 m (by omega)]
    ring
  · rw [reducedInvarDenom_of_emod_six_eq_one b c d m h, h6 (m - 1) (by omega)]
    ring
  · rw [reducedInvarDenom_of_emod_six_eq_two b c d m h,
      h3 (m + 1) (by omega), h2 m (by omega)]
    ring
  · rw [reducedInvarDenom_of_emod_six_eq_three b c d m h,
      h3 m (by omega), h2 (m - 1) (by omega)]
    ring
  · rw [reducedInvarDenom_of_emod_six_eq_four b c d m h,
      h3 (m - 1) (by omega), h2 m (by omega)]
    ring
  · rw [reducedInvarDenom_of_emod_six_eq_five b c d m h, h6 (m + 1) (by omega)]
    ring
/-- **The cancellation reducedInvarNum is named for**: the invariant numerator at s = 1
is reducedInvarNum times b. -/
@[simp high]
theorem invarNum_normEDS_one_eq_reducedInvarNum_mul (b c d : R) (m : ℤ) :
    invarNum (_root_.normEDS b c d) 1 m = reducedInvarNum b c d m * b := by
  simp_rw [reducedInvarNum_def, right_distrib, complEDS₂_mul_b, mul_assoc 2 _ b,
    complEDS₂Aux_mul_b]
  simp [invarNum_def]
  ring
end IsEllipticNet
namespace WeierstrassCurve
open MvPolynomial NormEDSParam
open scoped nonZeroDivisors
variable {R : Type*} [CommRing R] {b c d : R} (m : ℤ)
private theorem reducedInvarNum_eq_reducedInvarDenom_mul_of_mem
    (hb : b ∈ R⁰) (hc : c ∈ R⁰) :
    reducedInvarNum b c d m = reducedInvarDenom b c d m * (d + b ^ 4) := by
  rw [← mul_cancel_right_mem_nonZeroDivisors hb, ← mul_cancel_right_mem_nonZeroDivisors hc,
    ← IsEllipticNet.invarNum_normEDS_one_eq_reducedInvarNum_mul,
    IsEllipticNet.invarNum_normEDS_one_mul_eq_invarDenom_mul,
    IsEllipticNet.invarDenom_normEDS_one_eq_reducedInvarDenom_mul]
  ring
/-- **The reduced invariant identity**: reducedInvarNum = reducedInvarDenom * (d + b^4),
with no hypothesis on b, c, d. -/
@[simp]
theorem reducedInvarNum_eq_reducedInvarDenom_mul (b c d : R) (m : ℤ) :
    reducedInvarNum b c d m = reducedInvarDenom b c d m * (d + b ^ 4) := by
  have huniv := reducedInvarNum_eq_reducedInvarDenom_mul_of_mem
    (b := (X B : MvPolynomial NormEDSParam ℤ)) (c := X C) (d := X D) (m := m)
    (mem_nonZeroDivisors_of_ne_zero (X_ne_zero (R := ℤ) B))
    (mem_nonZeroDivisors_of_ne_zero (X_ne_zero (R := ℤ) C))
  simpa only [map_reducedInvarNum, map_reducedInvarDenom', map_mul, map_add, map_pow,
    MvPolynomial.aeval_X] using congr(aeval (NormEDSParam.rec b c d) $huniv)
end WeierstrassCurve
namespace WeierstrassCurve
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
/-- The invariant polynomial 6 X^2 + b2 X + b4 of a Weierstrass curve. -/
noncomputable def invar : R[X] := 6 * X ^ 2 + C W.b₂ * X + C W.b₄
theorem invar_def : W.invar = 6 * X ^ 2 + C W.b₂ * X + C W.b₄ := (rfl)
/-- The identity that pins invar down: prePsi4 + Psi2Sq^2 = invar * Psi3. -/
theorem preΨ₄_add_Ψ₂Sq_sq : W.preΨ₄ + W.Ψ₂Sq ^ 2 = W.invar * W.Ψ₃ := by
  rw [preΨ₄, Ψ₂Sq, invar, Ψ₃]
  linear_combination (norm := (simp only [map_ofNat, C_sub, C_mul, C_pow]; ring_nf))
    congr(C $W.b_relation) * (@X R _) ^ 2
/-- The bivariate form of prePsi4 + Psi2Sq^2 = invar * Psi3. -/
theorem preΨ₄_add_ψ₂_pow_four : C W.preΨ₄ + W.ψ₂ ^ 4 =
    C (W.invar * W.Ψ₃) + 8 * Affine.polynomial W * (2 * Affine.polynomial W + C W.Ψ₂Sq) := by
  simp_rw [show 4 = 2 * 2 by rfl, pow_mul, ψ₂_sq, add_sq, ← add_assoc, ← C_pow, ← C_add,
    preΨ₄_add_Ψ₂Sq_sq]
  simp only [C_mul]
  ring
/-- The division polynomials meet the invariant denominator: phi n * psi n = X psi(n)^3 - invarDenom. -/
theorem φ_mul_ψ (n : ℤ) :
    W.φ n * W.ψ n = C X * W.ψ n ^ 3 - IsEllipticNet.invarDenom W.ψ 1 n := by
  rw [WeierstrassCurve.φ, IsEllipticNet.invarDenom_def]
  ring
/-- The bivariate psi is Mathlib's normEDS at the curve parameters. -/
theorem ψ_eq_normEDS : W.ψ = normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) := rfl
/-- The second complement read off the reduced numerator. -/
theorem complEDS₂_eq_reducedInvarNum_sub (b c d : R) (m : ℤ) :
    complEDS₂ b c d m =
      reducedInvarNum b c d m - normEDS b c d m ^ 3 * b - 2 * complEDS₂Aux b c d m := by
  rw [reducedInvarNum_def]; ring
/-- **The defining identity of omega**: 2 omega n + a1 phi n psi n + a3 psi n^3 = psi_c n. -/
theorem ω_spec (n : ℤ) :
    2 * W.ω n + CC W.a₁ * W.φ n * W.ψ n + CC W.a₃ * W.ψ n ^ 3 = W.ψc n := by
  rw [ψc_def, complEDS₂_eq_reducedInvarNum_sub, reducedInvarNum_eq_reducedInvarDenom_mul,
    preΨ₄_add_ψ₂_pow_four, mul_assoc (C _), φ_mul_ψ, ψ_eq_normEDS,
    IsEllipticNet.invarDenom_normEDS_one_eq_reducedInvarDenom_mul, ω_def, ← ψ_eq_normEDS]
  simp only [invar_def, b₂, b₄, ψ₂, Affine.polynomialY, Affine.polynomialX,
    Affine.negPolynomial, map_ofNat, C_add, C_mul, C_pow]
  ring1
/-- omega_spec solved for 2 omega n. -/
theorem two_mul_ω (n : ℤ) :
    2 * W.ω n = W.ψc n - CC W.a₁ * W.φ n * W.ψ n - CC W.a₃ * W.ψ n ^ 3 := by
  rw [← ω_spec]; abel
end WeierstrassCurve
end
