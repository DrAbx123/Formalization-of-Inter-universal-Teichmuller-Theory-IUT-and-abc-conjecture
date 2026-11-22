/-
Copyright (c) 2026 The IUT Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT/ABC bridge batch (worker dsh_legendre_ratfunc)
-/
module

public import Mathlib.FieldTheory.RatFunc.Defs
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.FieldTheory.RatFunc.Degree
public import Mathlib.Tactic
public import Mathlib.Tactic.ComputeDegree

/-!
# The Legendre `j`-function `256 * (X ^ 2 - X + 1) ^ 3 / (X ^ 2 * (1 - X) ^ 2)`

This file realizes the *actual* Legendre `j`-invariant rational map as an element of the
Mathlib rational-function field `RatFunc K` over a field `K` of characteristic zero, and
extracts the arithmetic data that the IUT IV moduli/height specialization consumes:

* the numerator `256 * (X ^ 2 - X + 1) ^ 3` and the denominator `X ^ 2 * (1 - X) ^ 2` are
  coprime, and they *are* the `RatFunc.num` / `RatFunc.denom` pair of the map;
* the numerator has degree `6`, the denominator degree `4`, so the degree of the rational map
  `max (natDegree num) (natDegree denom)` is `6`, while the Mathlib library invariant
  `RatFunc.intDegree` is `6 - 4 = 2` (the order of the pole at infinity);
* the special-fibre numerator identity
  `256 * Q ^ 3 - 1728 * X ^ 2 * (1 - X) ^ 2 = 64 * (X + 1) ^ 2 * (X - 2) ^ 2 * (2 * X - 1) ^ 2`
  where `Q = X ^ 2 - X + 1`, checked by expansion of both sides;
* pole multiplicities at `0` and `1`, the multiplicity of the roots of `Q`, the order at
  infinity, and the multiplicities of the three points `-1`, `2`, `1 / 2` in the fibre over
  `1728`.

Everything is stated about the genuine `RatFunc` object and the actual polynomial
`Polynomial.rootMultiplicity` / `RatFunc.intDegree` API. No divisor object is introduced and no
modular-curve identification or ramification statement is claimed: the finite pole/zero data are
exact polynomial multiplicity statements.

Status: candidate proof source for the current implementation batch. It has *not* been compiled,
Lake-built or axiom-audited in this batch; the consumer project performs that at the batch
checkpoint. Exact API-application uncertainties are listed in the worker research log
`logs/coordination/direct-batch-dsh-ratfunc-20261015.md`.
-/

@[expose] public section

noncomputable section

open Polynomial
open scoped Polynomial RatFunc

namespace IUT.ABCBridge.Geometry

universe u

/-! ## A small `Polynomial.rootMultiplicity` toolbox

These are the exact order-theoretic facts needed for the pole and fibre computations below;
they are stated for an arbitrary field. -/

section Toolbox

variable {K : Type u} [Field K]

/-- `Polynomial.rootMultiplicity` is multiplicative under powers. -/
lemma legendre_rootMultiplicity_pow (p : K[X]) (hp : p ≠ 0) (a : K) (n : ℕ) :
    rootMultiplicity a (p ^ n) = n * rootMultiplicity a p := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero n hp) hp), ih,
        Nat.succ_mul]

/-- A nonzero constant factor does not change any root multiplicity. -/
lemma legendre_rootMultiplicity_C_mul {c : K} (hc : c ≠ 0) {p : K[X]} (hp : p ≠ 0)
    (a : K) : rootMultiplicity a (C c * p) = rootMultiplicity a p := by
  rw [rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr hc) hp), rootMultiplicity_C,
    zero_add]

/-- `a` is not a root of `(X - b) ^ n` when `a ≠ b`. -/
lemma legendre_rootMultiplicity_X_sub_C_pow_ne (a b : K) (h : a ≠ b) (n : ℕ) :
    rootMultiplicity a ((X - C b) ^ n) = 0 := by
  classical
  rw [legendre_rootMultiplicity_pow (X - C b) (monic_X_sub_C b).ne_zero a n,
    rootMultiplicity_X_sub_C, if_neg h, mul_zero]

/-- `a` is a root of `(X - a) ^ n` of multiplicity exactly `n`. -/
lemma legendre_rootMultiplicity_X_sub_C_pow_self (a : K) (n : ℕ) :
    rootMultiplicity a ((X - C a) ^ n) = n :=
  rootMultiplicity_X_sub_C_pow a n

/-- A nonzero constant factor does not change the root multiplicities of a threefold product
`C c * p * q * r`. -/
lemma legendre_rootMultiplicity_C_mul_three {c : K} (hc : c ≠ 0) {p q r : K[X]}
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (a : K) :
    rootMultiplicity a (C c * p * q * r) =
      rootMultiplicity a p + rootMultiplicity a q + rootMultiplicity a r := by
  have hpq : C c * p * q ≠ 0 := mul_ne_zero (mul_ne_zero (C_ne_zero.mpr hc) hp) hq
  have hpqr : C c * p * q * r ≠ 0 := mul_ne_zero hpq hr
  rw [rootMultiplicity_mul hpqr, rootMultiplicity_mul hpq,
    rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr hc) hp), rootMultiplicity_C, zero_add]

/-- A nonzero constant polynomial is coprime to every polynomial. -/
lemma legendre_isCoprime_C_of_ne_zero {c : K} (hc : c ≠ 0) (p : K[X]) :
    IsCoprime (C c) p := by
  refine ⟨C c⁻¹, 0, ?_⟩
  have h : (C c⁻¹ : K[X]) * C c = 1 := by
    rw [← C_mul, inv_mul_cancel₀ hc, C_1]
  rw [h, zero_mul, add_zero]

/-- Reduction lemma for fractions already in lowest terms: if `p` and `q` are coprime,
`q ≠ 0` and `q` is monic, then `p / q` already is the `RatFunc.num` / `RatFunc.denom`
normal form. -/
lemma legendre_num_denom_eq_of_isCoprime_monic {p q : K[X]} (hq : q ≠ 0) (hmonic : q.Monic)
    (hcop : IsCoprime p q) :
    (algebraMap K[X] K⟮X⟯ p / algebraMap K[X] K⟮X⟯ q).num = p ∧
      (algebraMap K[X] K⟮X⟯ p / algebraMap K[X] K⟮X⟯ q).denom = q := by
  set x : K⟮X⟯ := algebraMap K[X] K⟮X⟯ p / algebraMap K[X] K⟮X⟯ q with hxdef
  have hxq : x.num * q = p * x.denom :=
    (RatFunc.num_mul_eq_mul_denom_iff (x := x) hq).mpr hxdef
  have hq_dvd : q ∣ x.denom :=
    hcop.symm.dvd_of_dvd_mul_left ⟨x.num, by rw [← hxq, mul_comm]⟩
  have hden_dvd : x.denom ∣ q :=
    (RatFunc.isCoprime_num_denom x).symm.dvd_of_dvd_mul_left ⟨p, by rw [hxq, mul_comm]⟩
  have hle1 : q.natDegree ≤ x.denom.natDegree :=
    natDegree_le_of_dvd hq_dvd (RatFunc.denom_ne_zero x)
  obtain ⟨c, hc⟩ := hq_dvd
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    exact (RatFunc.monic_denom x).ne_zero hc
  have hle2 : x.denom.natDegree ≤ q.natDegree := natDegree_le_of_dvd hden_dvd hq
  have hdeg : q.natDegree = x.denom.natDegree := le_antisymm hle1 hle2
  have hcdeg : c.natDegree = 0 := by
    have hmul := natDegree_mul hq hc0
    rw [← hc, ← hdeg] at hmul
    omega
  have hclc : c.leadingCoeff = 1 := by
    have hlc := congrArg Polynomial.leadingCoeff hc
    rw [Polynomial.leadingCoeff_mul, hmonic.leadingCoeff, (RatFunc.monic_denom x).leadingCoeff,
      one_mul] at hlc
    exact hlc.symm
  have hccoeff : c.coeff 0 = 1 := by
    rw [← hcdeg, Polynomial.coeff_natDegree, hclc]
  have hc_eq : c = 1 := by
    rw [Polynomial.eq_C_of_natDegree_eq_zero hcdeg, hccoeff, Polynomial.C_1]
  have hden : x.denom = q := by rw [hc, hc_eq, mul_one]
  have hnum : x.num = p := by
    have h : x.num * q = p * q := by rw [hxq, hden]
    exact mul_right_cancel₀ hq h
  exact ⟨hnum, hden⟩

end Toolbox

/-! ## The Legendre `j`-function, its normal form, and the degree invariants -/

section Legendre

variable (K : Type u) [Field K] [CharZero K]

/-- The palindromic quadratic `Q = X ^ 2 - X + 1`, whose roots are the primitive sixth roots
of unity. -/
def legendreQuadratic : K[X] := X ^ 2 - X + 1

/-- The numerator polynomial `256 * (X ^ 2 - X + 1) ^ 3` of the Legendre `j`-function. -/
def legendreJNum : K[X] := C 256 * legendreQuadratic K ^ 3

/-- The denominator polynomial `X ^ 2 * (1 - X) ^ 2` of the Legendre `j`-function. -/
def legendreJDen : K[X] := X ^ 2 * (1 - X) ^ 2

/-- The Legendre `j`-function as an element of the rational-function field `K⟮X⟯`. -/
def legendreJ : K⟮X⟯ :=
  algebraMap K[X] K⟮X⟯ (legendreJNum K) / algebraMap K[X] K⟮X⟯ (legendreJDen K)

/-- The numerator of `J - 1728` over the common denominator `legendreJDen`,
written in the factorized form `64 * (X + 1) ^ 2 * (X - 2) ^ 2 * (2 * X - 1) ^ 2` (with
`X + 1` displayed as `X - (-1)` so that the root-multiplicity lemmas apply directly). -/
def legendreJ1728Num : K[X] :=
  C 64 * (X - C (-1)) ^ 2 * (X - C 2) ^ 2 * (C 2 * X - 1) ^ 2

/-- The degree of the rational map `J`, i.e. `max (natDegree num) (natDegree denom)`.
This is *not* the same invariant as Mathlib's `RatFunc.intDegree`, which is the difference of
the two degrees; both invariants are recorded below. -/
def legendreJMapDegree : ℕ := max (legendreJNum K).natDegree (legendreJDen K).natDegree

lemma legendreQuadratic_natDegree : (legendreQuadratic K).natDegree = 2 := by
  rw [legendreQuadratic]
  compute_degree!

lemma legendreQuadratic_ne_zero : legendreQuadratic K ≠ 0 := by
  intro h
  have h2 := legendreQuadratic_natDegree K
  rw [h, natDegree_zero] at h2
  exact (by norm_num : (0 : ℕ) ≠ 2) h2

lemma legendreJNum_natDegree : (legendreJNum K).natDegree = 6 := by
  rw [legendreJNum, natDegree_mul (C_ne_zero.mpr (by norm_num : (256 : K) ≠ 0))
    (pow_ne_zero 3 (legendreQuadratic_ne_zero K)), natDegree_C, zero_add, legendreQuadratic]
  compute_degree!

lemma legendreJDen_natDegree : (legendreJDen K).natDegree = 4 := by
  rw [legendreJDen]
  compute_degree!

lemma legendreJDen_monic : (legendreJDen K).Monic := by
  rw [legendreJDen]
  have hsq : ((1 : K[X]) - X) ^ 2 = (X - C (1 : K)) ^ 2 := by
    rw [← C_1]
    ring
  rw [hsq]
  exact (monic_X.pow 2).mul ((monic_X_sub_C 1).pow 2)

lemma legendreJNum_ne_zero : legendreJNum K ≠ 0 := by
  rw [legendreJNum]
  exact mul_ne_zero (C_ne_zero.mpr (by norm_num : (256 : K) ≠ 0))
    (pow_ne_zero 3 (legendreQuadratic_ne_zero K))

lemma legendreJDen_ne_zero : legendreJDen K ≠ 0 := (legendreJDen_monic K).ne_zero

lemma legendreJDen_algebraMap_ne_zero :
    algebraMap K[X] K⟮X⟯ (legendreJDen K) ≠ 0 :=
  RatFunc.algebraMap_ne_zero (legendreJDen_ne_zero K)

/-- `Q` is coprime to `X`, with the explicit Bézout identity `Q - (X - 1) * X = 1`. -/
lemma legendre_isCoprime_quadratic_X : IsCoprime (legendreQuadratic K) X := by
  rw [legendreQuadratic]
  exact ⟨1, -(X - 1), by ring⟩

/-- `Q` is coprime to `1 - X`, with the explicit Bézout identity `Q + X * (1 - X) = 1`. -/
lemma legendre_isCoprime_quadratic_one_sub_X : IsCoprime (legendreQuadratic K) (1 - X) := by
  rw [legendreQuadratic]
  exact ⟨1, X, by ring⟩

/-- The numerator and denominator polynomials of `J` are coprime. -/
lemma legendre_isCoprime_num_denom : IsCoprime (legendreJNum K) (legendreJDen K) := by
  have hX : IsCoprime ((legendreQuadratic K) ^ 3) (X ^ 2) :=
    ((legendre_isCoprime_quadratic_X K).pow_left (m := 3)).pow_right (n := 2)
  have h1X : IsCoprime ((legendreQuadratic K) ^ 3) (((1 : K[X]) - X) ^ 2) :=
    ((legendre_isCoprime_quadratic_one_sub_X K).pow_left (m := 3)).pow_right (n := 2)
  have hboth : IsCoprime ((legendreQuadratic K) ^ 3) (X ^ 2 * ((1 : K[X]) - X) ^ 2) :=
    hX.mul_right h1X
  have hconst : IsCoprime (C (256 : K)) (X ^ 2 * ((1 : K[X]) - X) ^ 2) :=
    legendre_isCoprime_C_of_ne_zero (by norm_num : (256 : K) ≠ 0) _
  have hfinal : IsCoprime (C (256 : K) * (legendreQuadratic K) ^ 3)
      (X ^ 2 * ((1 : K[X]) - X) ^ 2) := hconst.mul_left hboth
  simpa [legendreJNum, legendreJDen] using hfinal

/-- The `RatFunc.num` of `J` is the explicit numerator polynomial. -/
theorem legendreJ_num : (legendreJ K).num = legendreJNum K :=
  (legendre_num_denom_eq_of_isCoprime_monic (K := K) (legendreJDen_ne_zero K)
    (legendreJDen_monic K) (legendre_isCoprime_num_denom K)).1

/-- The `RatFunc.denom` of `J` is the explicit denominator polynomial. -/
theorem legendreJ_denom : (legendreJ K).denom = legendreJDen K :=
  (legendre_num_denom_eq_of_isCoprime_monic (K := K) (legendreJDen_ne_zero K)
    (legendreJDen_monic K) (legendre_isCoprime_num_denom K)).2

lemma legendreJ_ne_zero : legendreJ K ≠ 0 := by
  rw [legendreJ]
  exact div_ne_zero (RatFunc.algebraMap_ne_zero (legendreJNum_ne_zero K))
    (legendreJDen_algebraMap_ne_zero K)

lemma legendreJ_denom_monic : (legendreJ K).denom.Monic := by
  rw [legendreJ_denom]
  exact legendreJDen_monic K

/-- The `RatFunc.num` and `RatFunc.denom` of the Legendre `j`-map are coprime (the
specialization of `RatFunc.isCoprime_num_denom`). -/
lemma legendreJ_isCoprime_num_denom : IsCoprime (legendreJ K).num (legendreJ K).denom :=
  RatFunc.isCoprime_num_denom _

/-- Mathlib's `RatFunc.intDegree` of `J` is `deg num - deg denom = 6 - 4 = 2`; this is the
order of the pole of `J` at infinity. -/
theorem legendreJ_intDegree : (legendreJ K).intDegree = 2 := by
  rw [RatFunc.intDegree, legendreJ_num, legendreJ_denom, legendreJNum_natDegree,
    legendreJDen_natDegree]
  norm_num

/-- The rational-map degree `max (natDegree num) (natDegree denom)` of `J` is `6`. -/
theorem legendreJ_mapDegree : legendreJMapDegree K = 6 := by
  rw [legendreJMapDegree, legendreJNum_natDegree, legendreJDen_natDegree]
  norm_num

/-- Explicit form of `RatFunc.intDegree` for `J`: the difference of the two degrees, stated
separately so that no consumer confuses it with the rational-map degree. -/
theorem legendreJ_intDegree_eq_natDegree_sub :
    (legendreJ K).intDegree = ((legendreJNum K).natDegree : ℤ) - (legendreJDen K).natDegree := by
  rw [RatFunc.intDegree, legendreJ_num, legendreJ_denom]

end Legendre

/-! ## The fibre over `1728` -/

section Fibre

variable (K : Type u) [Field K] [CharZero K]

/-- The polynomial identity behind the `1728`-fibre, checked by expanding both sides:
`256 * Q ^ 3 - 1728 * X ^ 2 * (1 - X) ^ 2
  = 64 * (X + 1) ^ 2 * (X - 2) ^ 2 * (2 * X - 1) ^ 2`. -/
theorem legendreJNum_sub_1728_card :
    legendreJNum K - C (1728 : K) * legendreJDen K =
      C 64 * (X + 1) ^ 2 * (X - C 2) ^ 2 * (C 2 * X - 1) ^ 2 := by
  rw [legendreJNum, legendreJDen, legendreQuadratic]
  rw [Polynomial.C_ofNat (R := K) 256, Polynomial.C_ofNat (R := K) 1728,
    Polynomial.C_ofNat (R := K) 64, Polynomial.C_ofNat (R := K) 2]
  ring

/-- The named radical form `legendreJ1728Num` agrees with the expanded card above. -/
theorem legendreJ1728Num_card :
    legendreJ1728Num K =
      C 64 * (X + 1) ^ 2 * (X - C 2) ^ 2 * (C 2 * X - 1) ^ 2 := by
  rw [legendreJ1728Num]
  have h : (X - C (-1) : K[X]) = X + 1 := by
    rw [Polynomial.C_neg, Polynomial.C_1]
    ring
  rw [h]

/-- The polynomial identity in the named radical form:
`256 * Q ^ 3 - 1728 * X ^ 2 * (1 - X) ^ 2 = legendreJ1728Num`. -/
theorem legendreJNum_sub_1728 :
    legendreJNum K - C (1728 : K) * legendreJDen K = legendreJ1728Num K := by
  rw [legendreJNum_sub_1728_card K, legendreJ1728Num_card K]

/-- The rational-function form of the `1728`-fibre identity: subtracting `1728` from `J` puts
the numerator `legendreJ1728Num` over the common denominator `legendreJDen`. -/
theorem legendreJ_sub_1728 :
    legendreJ K - algebraMap K[X] K⟮X⟯ (C (1728 : K)) =
      algebraMap K[X] K⟮X⟯ (legendreJ1728Num K) / algebraMap K[X] K⟮X⟯ (legendreJDen K) := by
  rw [legendreJ]
  apply (eq_div_iff (legendreJDen_algebraMap_ne_zero K)).mpr
  rw [sub_mul, div_mul_cancel₀ _ (legendreJDen_algebraMap_ne_zero K), ← map_mul, ← map_sub,
    legendreJNum_sub_1728 K]

/-- The linear change of variable `2 * X - 1 = 2 * (X - 1 / 2)`. -/
lemma legendre_two_X_sub_one :
    (C 2 * X - 1 : K[X]) = C 2 * (X - C (1 / 2)) := by
  rw [mul_sub, ← C_mul, one_div, mul_inv_cancel₀ (by norm_num : (2 : K) ≠ 0), C_1]

lemma legendre_two_X_sub_one_ne_zero : (C 2 * X - 1 : K[X]) ≠ 0 := by
  rw [legendre_two_X_sub_one K]
  exact mul_ne_zero (C_ne_zero.mpr (by norm_num : (2 : K) ≠ 0))
    (monic_X_sub_C (1 / 2)).ne_zero

/-- `(2 * X - 1) ^ 2 = 4 * (X - 1 / 2) ^ 2`, so its root multiplicities are those of
`(X - 1 / 2) ^ 2`. -/
lemma legendre_rootMultiplicity_sq_two_X_sub_one (a : K) :
    rootMultiplicity a ((C 2 * X - 1 : K[X]) ^ 2) =
      2 * rootMultiplicity a (X - C (1 / 2)) := by
  have hC : (C (2 : K) : K[X]) ^ 2 = C 4 := by
    rw [← C_pow, show ((2 : K) ^ 2) = (4 : K) by norm_num]
  rw [legendre_two_X_sub_one K, mul_pow, hC,
    legendre_rootMultiplicity_C_mul (c := 4) (by norm_num : (4 : K) ≠ 0)
      (pow_ne_zero 2 (monic_X_sub_C (1 / 2)).ne_zero) a,
    legendre_rootMultiplicity_pow (X - C (1 / 2)) (monic_X_sub_C (1 / 2)).ne_zero a 2]

lemma legendreJ1728Num_ne_zero : legendreJ1728Num K ≠ 0 := by
  rw [legendreJ1728Num]
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero (C_ne_zero.mpr (by norm_num : (64 : K) ≠ 0))
        (pow_ne_zero 2 (monic_X_sub_C (-1)).ne_zero))
      (pow_ne_zero 2 (monic_X_sub_C (2 : K)).ne_zero))
    (pow_ne_zero 2 (legendre_two_X_sub_one_ne_zero K))

/-- The point `-1` of the fibre over `1728` has multiplicity exactly `2`. -/
theorem legendreJ1728Num_rootMultiplicity_neg_one :
    rootMultiplicity (-1) (legendreJ1728Num K) = 2 := by
  classical
  have h1 : rootMultiplicity (-1) ((X - C (-1)) ^ 2 : K[X]) = 2 :=
    legendre_rootMultiplicity_X_sub_C_pow_self (-1) 2
  have h2 : rootMultiplicity (-1) ((X - C (2 : K)) ^ 2 : K[X]) = 0 :=
    legendre_rootMultiplicity_X_sub_C_pow_ne (-1) 2 (by norm_num) 2
  have h3 : rootMultiplicity (-1) ((C 2 * X - 1 : K[X]) ^ 2) = 0 := by
    rw [legendre_rootMultiplicity_sq_two_X_sub_one K,
      rootMultiplicity_X_sub_C, if_neg (by norm_num : (-1 : K) ≠ 1 / 2), mul_zero]
  rw [legendreJ1728Num,
    legendre_rootMultiplicity_C_mul_three (c := 64) (by norm_num : (64 : K) ≠ 0)
      (pow_ne_zero 2 (monic_X_sub_C (-1)).ne_zero)
      (pow_ne_zero 2 (monic_X_sub_C (2 : K)).ne_zero)
      (pow_ne_zero 2 (legendre_two_X_sub_one_ne_zero K)) (-1),
    h1, h2, h3]

/-- The point `2` of the fibre over `1728` has multiplicity exactly `2`. -/
theorem legendreJ1728Num_rootMultiplicity_two :
    rootMultiplicity (2 : K) (legendreJ1728Num K) = 2 := by
  classical
  have h1 : rootMultiplicity (2 : K) ((X - C (-1)) ^ 2 : K[X]) = 0 :=
    legendre_rootMultiplicity_X_sub_C_pow_ne 2 (-1) (by norm_num) 2
  have h2 : rootMultiplicity (2 : K) ((X - C (2 : K)) ^ 2 : K[X]) = 2 :=
    legendre_rootMultiplicity_X_sub_C_pow_self 2 2
  have h3 : rootMultiplicity (2 : K) ((C 2 * X - 1 : K[X]) ^ 2) = 0 := by
    rw [legendre_rootMultiplicity_sq_two_X_sub_one K,
      rootMultiplicity_X_sub_C, if_neg (by norm_num : (2 : K) ≠ 1 / 2), mul_zero]
  rw [legendreJ1728Num,
    legendre_rootMultiplicity_C_mul_three (c := 64) (by norm_num : (64 : K) ≠ 0)
      (pow_ne_zero 2 (monic_X_sub_C (-1)).ne_zero)
      (pow_ne_zero 2 (monic_X_sub_C (2 : K)).ne_zero)
      (pow_ne_zero 2 (legendre_two_X_sub_one_ne_zero K)) 2,
    h1, h2, h3]

/-- The point `1 / 2` of the fibre over `1728` has multiplicity exactly `2`. -/
theorem legendreJ1728Num_rootMultiplicity_half :
    rootMultiplicity (1 / 2 : K) (legendreJ1728Num K) = 2 := by
  classical
  have h1 : rootMultiplicity (1 / 2 : K) ((X - C (-1)) ^ 2 : K[X]) = 0 :=
    legendre_rootMultiplicity_X_sub_C_pow_ne (1 / 2) (-1) (by norm_num) 2
  have h2 : rootMultiplicity (1 / 2 : K) ((X - C (2 : K)) ^ 2 : K[X]) = 0 :=
    legendre_rootMultiplicity_X_sub_C_pow_ne (1 / 2) 2 (by norm_num) 2
  have h3 : rootMultiplicity (1 / 2 : K) ((C 2 * X - 1 : K[X]) ^ 2) = 2 := by
    rw [legendre_rootMultiplicity_sq_two_X_sub_one K, rootMultiplicity_X_sub_C_self]
  rw [legendreJ1728Num,
    legendre_rootMultiplicity_C_mul_three (c := 64) (by norm_num : (64 : K) ≠ 0)
      (pow_ne_zero 2 (monic_X_sub_C (-1)).ne_zero)
      (pow_ne_zero 2 (monic_X_sub_C (2 : K)).ne_zero)
      (pow_ne_zero 2 (legendre_two_X_sub_one_ne_zero K)) (1 / 2),
    h1, h2, h3]

/-- Consolidated fibre data for the value `1728`: the three finite preimages `-1`, `2` and
`1 / 2` each occur with multiplicity exactly `2`. -/
theorem legendreJ1728_fibre_data :
    rootMultiplicity (-1) (legendreJ1728Num K) = 2 ∧
      rootMultiplicity (2 : K) (legendreJ1728Num K) = 2 ∧
      rootMultiplicity (1 / 2 : K) (legendreJ1728Num K) = 2 :=
  ⟨legendreJ1728Num_rootMultiplicity_neg_one K,
    legendreJ1728Num_rootMultiplicity_two K,
    legendreJ1728Num_rootMultiplicity_half K⟩

end Fibre

/-! ## Poles at `0`, `1` and at infinity -/

section Poles

variable (K : Type u) [Field K] [CharZero K]

/-- Rewriting the raw denominator as a product of linear factors centred at `0` and `1`. -/
lemma legendreJDen_eq_factors :
    legendreJDen K = (X - C (0 : K)) ^ 2 * (X - C (1 : K)) ^ 2 := by
  rw [legendreJDen]
  have hX : (X : K[X]) ^ 2 = (X - C (0 : K)) ^ 2 := by rw [C_0, sub_zero]
  have hsq : ((1 : K[X]) - X) ^ 2 = (X - C (1 : K)) ^ 2 := by
    rw [← C_1]
    ring
  rw [hX, hsq]

/-- The denominator vanishes at `0` to order exactly `2`. -/
theorem legendreJDen_rootMultiplicity_zero :
    rootMultiplicity (0 : K) (legendreJDen K) = 2 := by
  rw [legendreJDen_eq_factors K,
    rootMultiplicity_mul
      (mul_ne_zero (pow_ne_zero 2 (monic_X_sub_C (0 : K)).ne_zero)
        (pow_ne_zero 2 (monic_X_sub_C (1 : K)).ne_zero)),
    legendre_rootMultiplicity_X_sub_C_pow_self (0 : K) 2,
    legendre_rootMultiplicity_X_sub_C_pow_ne (0 : K) 1 (by norm_num) 2]

/-- The denominator vanishes at `1` to order exactly `2`. -/
theorem legendreJDen_rootMultiplicity_one :
    rootMultiplicity (1 : K) (legendreJDen K) = 2 := by
  rw [legendreJDen_eq_factors K,
    rootMultiplicity_mul
      (mul_ne_zero (pow_ne_zero 2 (monic_X_sub_C (0 : K)).ne_zero)
        (pow_ne_zero 2 (monic_X_sub_C (1 : K)).ne_zero)),
    legendre_rootMultiplicity_X_sub_C_pow_ne (1 : K) 0 (by norm_num) 2,
    legendre_rootMultiplicity_X_sub_C_pow_self (1 : K) 2]

/-- The numerator does not vanish at `0`, so `0` is a pole of `J` of order exactly `2`. -/
theorem legendreJNum_rootMultiplicity_zero :
    rootMultiplicity (0 : K) (legendreJNum K) = 0 := by
  apply rootMultiplicity_eq_zero
  intro hroot
  rw [IsRoot.def] at hroot
  simp [legendreJNum, legendreQuadratic] at hroot

/-- The numerator does not vanish at `1`, so `1` is a pole of `J` of order exactly `2`. -/
theorem legendreJNum_rootMultiplicity_one :
    rootMultiplicity (1 : K) (legendreJNum K) = 0 := by
  apply rootMultiplicity_eq_zero
  intro hroot
  rw [IsRoot.def] at hroot
  simp [legendreJNum, legendreQuadratic] at hroot

/-- The order of the pole of a rational function `x` at a finite point `a`, computed as
`rootMultiplicity a x.denom - rootMultiplicity a x.num`. Because `x.num` and `x.denom` are
coprime (`RatFunc.isCoprime_num_denom`), at most one of the two multiplicities is nonzero, so
the truncated natural-number subtraction is the honest order. -/
def ratFuncPoleOrder (x : K⟮X⟯) (a : K) : ℕ :=
  rootMultiplicity a x.denom - rootMultiplicity a x.num

/-- `J` has a pole of order `2` at `0`. -/
theorem legendreJ_poleOrder_zero : ratFuncPoleOrder K (legendreJ K) 0 = 2 := by
  rw [ratFuncPoleOrder, legendreJ_num, legendreJ_denom, legendreJDen_rootMultiplicity_zero K,
    legendreJNum_rootMultiplicity_zero K]

/-- `J` has a pole of order `2` at `1`. -/
theorem legendreJ_poleOrder_one : ratFuncPoleOrder K (legendreJ K) 1 = 2 := by
  rw [ratFuncPoleOrder, legendreJ_num, legendreJ_denom, legendreJDen_rootMultiplicity_one K,
    legendreJNum_rootMultiplicity_one K]

/-- `J` has a pole of order `2` at infinity, recorded as the exact value of the library
invariant `RatFunc.intDegree` (`= deg num - deg denom = 6 - 4`). -/
theorem legendreJ_infinity_poleOrder : (legendreJ K).intDegree = 2 :=
  legendreJ_intDegree K

/-- Consolidated finite/infinite pole data for `J`: poles of order `2` at `0`, at `1` and at
infinity, with no numerator cancellation at `0` or `1`. -/
theorem legendreJ_pole_data :
    ratFuncPoleOrder K (legendreJ K) 0 = 2 ∧
      ratFuncPoleOrder K (legendreJ K) 1 = 2 ∧
      (legendreJ K).intDegree = 2 :=
  ⟨legendreJ_poleOrder_zero K, legendreJ_poleOrder_one K, legendreJ_infinity_poleOrder K⟩

end Poles

/-! ## Zeros at the roots of `X ^ 2 - X + 1` -/

section QuadraticRoots

variable (K : Type u) [Field K] [CharZero K]

/-- Over a characteristic-zero field, a root `α` of `Q = X ^ 2 - X + 1` is a *simple* root:
`rootMultiplicity α Q = 1`. The conjugate root is `1 - α`, and characteristic zero forces
`α ≠ 1 - α` (otherwise `3 = 0`). -/
theorem legendreQuadratic_rootMultiplicity_of_root {α : K} (hα : α ^ 2 - α + 1 = 0) :
    rootMultiplicity α (legendreQuadratic K) = 1 := by
  classical
  have hprod : α * (1 - α) = 1 := by linear_combination -hα
  have hne : α ≠ 1 - α := by
    intro h
    have h2 : (2 : K) * α - 1 = 0 := by linear_combination h
    have h3 : (3 : K) = 0 := by
      linear_combination 4 * hα - ((2 : K) * α - 1) * h2
    exact (by norm_num : (3 : K) ≠ 0) h3
  have hfac : legendreQuadratic K = (X - C α) * (X - C (1 - α)) := by
    rw [legendreQuadratic]
    have hC1 : (C (1 - α) : K[X]) = 1 - C α := by rw [map_sub, map_one]
    have hkey : (X - C α) * (X - C (1 - α)) =
        (X : K[X]) ^ 2 - X + C α * C (1 - α) := by
      rw [hC1]
      ring
    rw [hkey, ← map_mul, hprod, C_1]
  rw [hfac,
    rootMultiplicity_mul
      (mul_ne_zero (monic_X_sub_C α).ne_zero (monic_X_sub_C (1 - α)).ne_zero),
    rootMultiplicity_X_sub_C_self, rootMultiplicity_X_sub_C, if_neg hne]

/-- A root `α` of `Q = X ^ 2 - X + 1` is a zero of the numerator of `J` of multiplicity
exactly `3` in characteristic zero. -/
theorem legendreJNum_rootMultiplicity_of_root {α : K} (hα : α ^ 2 - α + 1 = 0) :
    rootMultiplicity α (legendreJNum K) = 3 := by
  rw [legendreJNum,
    legendre_rootMultiplicity_C_mul (c := 256) (by norm_num : (256 : K) ≠ 0)
      (pow_ne_zero 3 (legendreQuadratic_ne_zero K)) α,
    legendre_rootMultiplicity_pow (legendreQuadratic K) (legendreQuadratic_ne_zero K) α 3,
    legendreQuadratic_rootMultiplicity_of_root K hα]

end QuadraticRoots

/-! ## Consolidated interface -/

section Interface

variable (K : Type u) [Field K] [CharZero K]

/-- Consolidated reduced-form data for the Legendre `j`-map: explicit numerator, explicit
denominator, coprimality, monicity of the denominator, the two polynomial degrees, the library
degree `RatFunc.intDegree` and the rational-map degree `max (deg num) (deg denom)`. -/
theorem legendreJ_reduced_data :
    (legendreJ K).num = legendreJNum K ∧
      (legendreJ K).denom = legendreJDen K ∧
      IsCoprime (legendreJNum K) (legendreJDen K) ∧
      (legendreJDen K).Monic ∧
      (legendreJNum K).natDegree = 6 ∧
      (legendreJDen K).natDegree = 4 ∧
      (legendreJ K).intDegree = 2 ∧
      legendreJMapDegree K = 6 :=
  ⟨legendreJ_num K, legendreJ_denom K, legendre_isCoprime_num_denom K, legendreJDen_monic K,
    legendreJNum_natDegree K, legendreJDen_natDegree K, legendreJ_intDegree K,
    legendreJ_mapDegree K⟩

end Interface

end IUT.ABCBridge.Geometry
