/-
Copyright (c) 2026 The IUT/ABC formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT/ABC formalization project
-/

import tmp.sheaf.xif.paper.S1373ZeroCriterionActual

/-!
# S1378: the general division-polynomial zero criterion

Let W be a Weierstrass curve over a field F, and let psi_n be Mathlib's
n-division polynomial.  The zero criterion is

  psi_n(P) = 0 <-> n . P = 0  for every point P of W,

equivalently, the root set of psi_n is exactly the n-torsion subgroup.
S1373 proves this criterion unconditionally for n = 2 and n = 3; this file
attacks the general case.

## What is proved here, with no axioms, sorry, admit or opaque declaration

1. **The root-counting reduction for odd n.**
   s1378RootsAreTorsion_of_detection_cardinality: if

   * (detection) every n-torsion point is a root of psi_n, and
   * (cardinality) the n-torsion is a finite set T with T.card = n^2,

   then every root of psi_n is n-torsion.  The proof is the honest root-count:
   the map P |-> x(P) from T \ {O} lands in the roots of the odd division
   polynomial, its fibres have at most two points (P and -P), while the
   roots number at most the degree (n^2-1)/2.  Hence the image is *all* roots,
   so a root point P has the same x-coordinate as some n-torsion point Q,
   and P = Q or P = -Q.

   Consequently s1378ZeroCriterion_of_detection_cardinality gives the full
   criterion from detection plus cardinality.  This is a real reduction: no
   direction of the criterion is assumed and the statement is closed by a
   counting argument.

2. **The exact first input, isolated as a proposition.**
   s1378OddZeroCriterionInput W n is the conjunction of the two missing
   inputs above (detection and cardinality).  It is a def : Prop; it is not
   inhabited, and no axiom or placeholder is introduced for it.  The theorem
   s1378ZeroCriterion_of_input proves that this input implies the general
   odd-n zero criterion.

3. **The even induction step.**
   s1378OmegaIdentity is the cleared point-level omega identity
   psi_2(mP) * psi_m(P)^4 = psi_{2m}(P) (where psi_2(mP) is read through the
   2-division polynomial of the point mP).
   s1378ZeroCriterion_two_mul_of_omega proves that this identity at m, together
   with the zero criterion at m, gives the zero criterion at 2m.

4. **The identity at m = 2, and the new case n = 4.**
   s1378OmegaIdentity_two proves the point-level syzygy
   psi_2(2P) * psi_2(P)^4 = psi_4(P) unconditionally, by the tangent/doubling
   computation.  Combined with the induction step and the known n = 2
   criterion this yields divisionPolynomialZeroCriterion_four: the zero
   criterion is unconditional for n = 4 as well, in every characteristic.

## The exact remaining gap

For odd n other than 3 the two missing inputs are exactly
DivisionPolynomialDetectsTorsion W n (the forward half, already a named
interface in the tree) and s1378TorsionCardinality W n (the numerical
#W[n] = n^2).  Neither is assumed here.  The file therefore does NOT claim
the general odd-n criterion unconditionally; it proves the precise reduction
and the new unconditional instance n = 4.

## Main results

* s1378RootsAreTorsion_of_detection_cardinality
* s1378ZeroCriterion_of_detection_cardinality
* s1378ZeroCriterion_of_input
* s1378OmegaIdentity_two
* s1378ZeroCriterion_two_mul_of_omega
* divisionPolynomialZeroCriterion_four
* divisionPolynomialRootsAreTorsion_four, rootSet_four_eq_torsion

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, division polynomial, torsion point, zero criterion
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

noncomputable section

namespace WeierstrassCurve

section Field

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

/-! ## 1. The named inputs -/

/-- The numerical n-torsion input: the n-torsion points form a finite set of
cardinality n^2.  This is the precise form of the missing #W[n] = n^2. -/
def s1378TorsionCardinality (n : ℤ) : Prop :=
  ∃ T : Finset W.toAffine.Point, T.card = n.natAbs ^ 2 ∧
    ∀ P : W.toAffine.Point, P ∈ T ↔ n • P = 0

/-- The exact first input for the general odd-n zero criterion: detection plus
cardinality.  Neither conjunct is assumed or inhabited in this file. -/
def s1378OddZeroCriterionInput (n : ℤ) : Prop :=
  W.DivisionPolynomialDetectsTorsion n ∧ s1378TorsionCardinality W n

/-! ## 2. The root-counting reduction for odd n -/

/-- **Root counting for odd n.**  Detection plus cardinality imply the reverse
half of the zero criterion, in every characteristic.

The map P |-> x(P) sends the n^2 - 1 nonzero n-torsion points into the roots
of prePsi_n; each fibre has at most two elements, and the roots number at most
(n^2 - 1)/2.  Hence the image is the full root set. -/
theorem s1378RootsAreTorsion_of_detection_card
    {n : ℤ} (hodd : ¬ Even n) (hchar : (n : F) ≠ 0)
    (hdet : W.DivisionPolynomialDetectsTorsion n)
    (T : Finset W.toAffine.Point) (hTcard : T.card = n.natAbs ^ 2)
    (hTmem : ∀ P : W.toAffine.Point, P ∈ T ↔ n • P = 0) :
    W.DivisionPolynomialRootsAreTorsion n := by
  classical
  have hpre : W.preΨ n ≠ 0 := W.preΨ_ne_zero hchar
  let S : Finset F := (W.preΨ n).roots.toFinset
  let AS : Finset (Fin 2 → F) := S.image (fun x : F => ![x, 1])
  let AT : Finset (Fin 2 → F) := (T.erase 0).image (fun P => P.xRep)
  have hzeroT : (0 : W.toAffine.Point) ∈ T := (hTmem 0).mpr (by simp)
  have hErase : (T.erase 0).card = n.natAbs ^ 2 - 1 := by
    rw [Finset.card_erase_of_mem hzeroT, hTcard]
  have hSle : S.card ≤ (n.natAbs ^ 2 - 1) / 2 := by
    have h1 : S.card ≤ (W.preΨ n).natDegree := by
      calc S.card ≤ (W.preΨ n).roots.card := Multiset.toFinset_card_le _
        _ ≤ (W.preΨ n).natDegree := Polynomial.card_roots' _
    calc S.card ≤ (W.preΨ n).natDegree := h1
      _ ≤ (n.natAbs ^ 2 - if Even n then 4 else 1) / 2 := W.natDegree_preΨ_le n
      _ = (n.natAbs ^ 2 - 1) / 2 := by rw [if_neg hodd]
  have hmap : ∀ P ∈ T.erase 0, P.xRep ∈ AS := by
    intro P hP
    rw [Finset.mem_erase] at hP
    obtain ⟨hP0, hPT⟩ := hP
    have htors : n • P = 0 := (hTmem P).mp hPT
    rcases P with _ | ⟨u, v, hns⟩
    · exact absurd rfl hP0
    · have hroot : (W.preΨ n).eval u = 0 := by
        have h := hdet _ htors
        rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_some,
          W.evalDivisionPolynomial_eq_eval_preΨ_of_odd hns.1 hodd] at h
        exact h
      refine Finset.mem_image.mpr ⟨u, ?_, ?_⟩
      · rw [show S = (W.preΨ n).roots.toFinset from rfl, Multiset.mem_toFinset,
          Polynomial.mem_roots hpre, Polynomial.IsRoot.def]
        exact hroot
      · rw [WeierstrassCurve.Affine.Point.xRep_some]
  have hATsubAS : AT ⊆ AS := by
    intro z hz
    rw [show AT = (T.erase 0).image (fun P => P.xRep) from rfl, Finset.mem_image] at hz
    obtain ⟨P, hP, rfl⟩ := hz
    exact hmap P hP
  have hATle : AT.card ≤ AS.card := Finset.card_le_card hATsubAS
  have hASle : AS.card ≤ S.card := Finset.card_image_le
  have hfib : ∀ b ∈ AT, ((T.erase 0).filter (fun P => P.xRep = b)).card ≤ 2 := by
    intro b hb
    rcases Finset.eq_empty_or_nonempty ((T.erase 0).filter (fun P => P.xRep = b)) with
      hem | ⟨Q, hQ⟩
    · rw [hem]; simp
    · rw [Finset.mem_filter] at hQ
      have hsub : (T.erase 0).filter (fun P => P.xRep = b) ⊆ {Q, -Q} := by
        intro P hP
        rw [Finset.mem_filter] at hP
        have hx : P.xRep = Q.xRep := by rw [hP.2, hQ.2]
        rcases WeierstrassCurve.Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep hx with h | h
        · simp [h]
        · simp [h]
      calc ((T.erase 0).filter (fun P => P.xRep = b)).card
          ≤ ({Q, -Q} : Finset W.toAffine.Point).card := Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_le_two
  have hAle : (T.erase 0).card ≤ 2 * AT.card := by
    rw [show AT = (T.erase 0).image (fun P => P.xRep) from rfl]
    exact Finset.card_le_mul_card_image _ 2 hfib
  have hoddAbs : Odd n.natAbs := Int.natAbs_odd.mpr (Int.not_even_iff_odd.mp hodd)
  have hoddSq : Odd (n.natAbs ^ 2) := by
    rw [pow_two]; exact hoddAbs.mul hoddAbs
  have hdvd : 2 ∣ n.natAbs ^ 2 - 1 := (Nat.Odd.sub_odd hoddSq odd_one).two_dvd
  have htwo : 2 * ((n.natAbs ^ 2 - 1) / 2) = n.natAbs ^ 2 - 1 := Nat.mul_div_cancel' hdvd
  have hlow : n.natAbs ^ 2 - 1 ≤ 2 * AT.card := by
    calc n.natAbs ^ 2 - 1 = (T.erase 0).card := hErase.symm
      _ ≤ 2 * AT.card := hAle
  have hhigh : 2 * AT.card ≤ n.natAbs ^ 2 - 1 := by
    calc 2 * AT.card ≤ 2 * AS.card := Nat.mul_le_mul_left 2 hATle
      _ ≤ 2 * S.card := Nat.mul_le_mul_left 2 hASle
      _ ≤ 2 * ((n.natAbs ^ 2 - 1) / 2) := Nat.mul_le_mul_left 2 hSle
      _ = n.natAbs ^ 2 - 1 := htwo
  have hATEq : AT.card = AS.card := by omega
  have hATeqAS : AT = AS := Finset.eq_of_subset_of_card_le hATsubAS hATEq.ge
  intro P hP
  cases P with
  | zero => exact zsmul_zero n
  | some x y hns =>
      have hxS : x ∈ S := by
        rw [show S = (W.preΨ n).roots.toFinset from rfl, Multiset.mem_toFinset,
          Polynomial.mem_roots hpre, Polynomial.IsRoot.def]
        rw [← W.evalDivisionPolynomial_eq_eval_preΨ_of_odd hns.1 hodd]
        exact hP
      have hmemAS : ![x, 1] ∈ AS := Finset.mem_image.mpr ⟨x, hxS, rfl⟩
      rw [← hATeqAS] at hmemAS
      obtain ⟨Q, hQ, hQx⟩ := Finset.mem_image.mp hmemAS
      rw [Finset.mem_erase] at hQ
      have hQtors : n • Q = 0 := (hTmem Q).mp hQ.2
      have hxRep : (WeierstrassCurve.Affine.Point.some x y hns).xRep = Q.xRep := by
        rw [WeierstrassCurve.Affine.Point.xRep_some, hQx]
      rcases WeierstrassCurve.Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep hxRep with h | h
      · rw [h]; exact hQtors
      · rw [h, zsmul_neg, hQtors, neg_zero]

/-- **The reverse criterion from detection plus cardinality.** -/
theorem s1378RootsAreTorsion_of_detection_cardinality
    {n : ℤ} (hodd : ¬ Even n) (hchar : (n : F) ≠ 0)
    (hdet : W.DivisionPolynomialDetectsTorsion n)
    (hcard : s1378TorsionCardinality W n) :
    W.DivisionPolynomialRootsAreTorsion n := by
  obtain ⟨T, hTcard, hTmem⟩ := hcard
  exact s1378RootsAreTorsion_of_detection_card W hodd hchar hdet T hTcard hTmem

/-- **The full zero criterion from detection plus cardinality.**  This is the
precise reduction of the general odd-n criterion to the two named inputs. -/
theorem s1378ZeroCriterion_of_detection_cardinality
    {n : ℤ} (hodd : ¬ Even n) (hchar : (n : F) ≠ 0)
    (hdet : W.DivisionPolynomialDetectsTorsion n)
    (hcard : s1378TorsionCardinality W n) :
    W.DivisionPolynomialZeroCriterion n := by
  intro P
  exact ⟨hdet P, s1378RootsAreTorsion_of_detection_cardinality W hodd hchar hdet hcard P⟩

/-- **The exact first lemma, applied.**  The input detection and cardinality
implies the general odd-n zero criterion. -/
theorem s1378ZeroCriterion_of_input
    {n : ℤ} (hodd : ¬ Even n) (hchar : (n : F) ≠ 0)
    (h : s1378OddZeroCriterionInput W n) :
    W.DivisionPolynomialZeroCriterion n :=
  s1378ZeroCriterion_of_detection_cardinality W hodd hchar h.1 h.2

/-! ## 3. The point-level omega identity and the even induction step -/

/-- The value of psi_2 at a point, with value 0 at the point at infinity. -/
noncomputable def s1378WCoord : W.toAffine.Point → F
  | .zero => 0
  | .some x y _ => 2 * y + W.a₁ * x + W.a₃

@[simp]
lemma s1378WCoord_zero : s1378WCoord W (0 : W.toAffine.Point) = 0 := rfl

@[simp]
lemma s1378WCoord_some {x y : F} (h : W.toAffine.Nonsingular x y) :
    s1378WCoord W (WeierstrassCurve.Affine.Point.some x y h) =
      2 * y + W.a₁ * x + W.a₃ := rfl

/-- psi_2(Q) = 0 is exactly 2 . Q = 0, in wCoord form. -/
lemma s1378WCoord_eq_zero_iff_two_zsmul (Q : W.toAffine.Point) :
    s1378WCoord W Q = 0 ↔ (2 : ℤ) • Q = 0 := by
  cases Q with
  | zero => exact iff_of_true rfl (zsmul_zero 2)
  | some x y h =>
      rw [s1378WCoord_some, ← WeierstrassCurve.evalDivisionPolynomial_two]
      have h2 := (W.two_nsmul_eq_zero_iff_evalDivisionPolynomialAtPoint_two_eq_zero
        (WeierstrassCurve.Affine.Point.some x y h))
      rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_some] at h2
      rw [show (2 : ℤ) • WeierstrassCurve.Affine.Point.some x y h =
        (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y h from natCast_zsmul _ 2]
      exact h2.symm

/-- The cleared point-level omega identity at m:
s1378WCoord (m . P) * psi_m(P)^4 = psi_{2m}(P) for every point P. -/
def s1378OmegaIdentity (m : ℤ) : Prop :=
  ∀ P : W.toAffine.Point,
    s1378WCoord W (m • P) * (W.evalDivisionPolynomialAtPoint m P) ^ 4 =
      W.evalDivisionPolynomialAtPoint (2 * m) P

/-- **The even induction step.**  The omega identity at m plus the zero criterion
at m give the zero criterion at 2m. -/
theorem s1378ZeroCriterion_two_mul_of_omega
    {m : ℤ} (hω : s1378OmegaIdentity W m)
    (hcrit : W.DivisionPolynomialZeroCriterion m) :
    W.DivisionPolynomialZeroCriterion (2 * m) := by
  intro P
  constructor
  · intro h
    have hQ : (2 : ℤ) • (m • P) = 0 := by
      rwa [show (2 * m) • P = (2 : ℤ) • (m • P) by rw [mul_zsmul]] at h
    have hw : s1378WCoord W (m • P) = 0 :=
      (s1378WCoord_eq_zero_iff_two_zsmul W (m • P)).mpr hQ
    have h2 := hω P
    rw [hw, zero_mul] at h2
    exact h2.symm
  · intro hψ
    have h2 := hω P
    rw [hψ] at h2
    by_cases hm : W.evalDivisionPolynomialAtPoint m P = 0
    · have hmP : m • P = 0 := (hcrit P).mpr hm
      rw [show (2 * m) • P = (2 : ℤ) • (m • P) by rw [mul_zsmul], hmP, zsmul_zero]
    · have hpow : (W.evalDivisionPolynomialAtPoint m P) ^ 4 ≠ 0 := pow_ne_zero 4 hm
      have hw : s1378WCoord W (m • P) = 0 := (mul_eq_zero.mp h2).resolve_right hpow
      have hQ : (2 : ℤ) • (m • P) = 0 :=
        (s1378WCoord_eq_zero_iff_two_zsmul W (m • P)).mp hw
      rwa [show (2 * m) • P = (2 : ℤ) • (m • P) by rw [mul_zsmul]]

/-- The reverse half of the even induction step. -/
theorem s1378RootsAreTorsion_two_mul_of_omega
    {m : ℤ} (hω : s1378OmegaIdentity W m)
    (hroot : W.DivisionPolynomialRootsAreTorsion m) :
    W.DivisionPolynomialRootsAreTorsion (2 * m) := by
  intro P hψ
  have h2 := hω P
  rw [hψ] at h2
  by_cases hm : W.evalDivisionPolynomialAtPoint m P = 0
  · have hmP : m • P = 0 := hroot P hm
    rw [show (2 * m) • P = (2 : ℤ) • (m • P) by rw [mul_zsmul], hmP, zsmul_zero]
  · have hpow : (W.evalDivisionPolynomialAtPoint m P) ^ 4 ≠ 0 := pow_ne_zero 4 hm
    have hw : s1378WCoord W (m • P) = 0 := (mul_eq_zero.mp h2).resolve_right hpow
    have hQ : (2 : ℤ) • (m • P) = 0 :=
      (s1378WCoord_eq_zero_iff_two_zsmul W (m • P)).mp hw
    rwa [show (2 * m) • P = (2 : ℤ) • (m • P) by rw [mul_zsmul]]

/-! ## 4. The tangent syzygy at n = 2, and n = 4 -/

/-- The doubling equation cleared for B^3. -/
private lemma s1378_w_mul_B_cube {x y A B : F}
    (hA : A = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y)
    (hBdef : B = 2 * y + W.a₁ * x + W.a₃)
    (hB : B ≠ 0) :
    (2 * W.toAffine.addY x x y (W.toAffine.slope x x y y)
        + W.a₁ * W.toAffine.addX x x (W.toAffine.slope x x y y) + W.a₃)
      * B ^ 3 =
    -2 * A * (A ^ 2 + W.a₁ * A * B - (W.a₂ + 3 * x) * B ^ 2)
      - W.a₁ * (A ^ 2 + W.a₁ * A * B - (W.a₂ + 2 * x) * B ^ 2) * B
      - B ^ 4 + W.a₁ * x * B ^ 3 := by
  have hyne : y ≠ W.toAffine.negY x y := by
    intro hy
    apply hB
    rw [hBdef]
    rw [WeierstrassCurve.Affine.negY] at hy
    linear_combination hy
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hyne]
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.negAddY]
  have hyB' : y - (-y - W.a₁ * x - W.a₃) = B := by
    rw [hBdef]; ring
  rw [hyB']
  rw [hA]
  field_simp [hB]
  rw [hBdef]
  ring

/-- The expanded prePsi_4 in terms of the doubling data. -/
private lemma s1378_preΨ₄_eq_R {x y A B : F}
    (hE : y ^ 2 + W.a₁ * x * y + W.a₃ * y -
      (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0)
    (hA : A = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y)
    (hBdef : B = 2 * y + W.a₁ * x + W.a₃) :
    (W.preΨ₄).eval x =
    -2 * A * (A ^ 2 + W.a₁ * A * B - (W.a₂ + 3 * x) * B ^ 2)
      - W.a₁ * (A ^ 2 + W.a₁ * A * B - (W.a₂ + 2 * x) * B ^ 2) * B
      - B ^ 4 + W.a₁ * x * B ^ 3 := by
  rw [hA, hBdef]
  rw [WeierstrassCurve.preΨ₄]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_ofNat,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  linear_combination (norm := ring_nf)
    (-56 * x ^ 3 - (10 * W.a₁ ^ 2 + 56 * W.a₂) * x ^ 2
      + (-W.a₁ ^ 4 - 8 * W.a₁ ^ 2 * W.a₂ + 4 * W.a₁ * W.a₃ + 16 * W.a₁ * y
          - 16 * W.a₂ ^ 2 - 8 * W.a₄) * x
      + (-W.a₁ ^ 3 * W.a₃ - 2 * W.a₁ ^ 2 * W.a₄ - 4 * W.a₁ * W.a₂ * W.a₃
          - 8 * W.a₂ * W.a₄ + 8 * W.a₃ ^ 2 + 16 * W.a₃ * y + 16 * W.a₆ + 16 * y ^ 2)) * hE

/-- **Doubling syzygy.**  Away from psi_2(P) = 0,
prePsi_4(x(P)) = psi_2(2P) * psi_2(P)^3. -/
theorem s1378_preΨ₄_eq_w_two_mul {x y : F} (h : W.toAffine.Nonsingular x y)
    (hB : 2 * y + W.a₁ * x + W.a₃ ≠ 0) :
    (W.preΨ₄).eval x =
      (2 * W.toAffine.addY x x y (W.toAffine.slope x x y y)
        + W.a₁ * W.toAffine.addX x x (W.toAffine.slope x x y y) + W.a₃)
      * (2 * y + W.a₁ * x + W.a₃) ^ 3 := by
  have hE : y ^ 2 + W.a₁ * x * y + W.a₃ * y -
      (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 :=
    (WeierstrassCurve.Affine.equation_iff' (W := W.toAffine) x y).mp h.1
  set A : F := 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y with hA
  set B : F := 2 * y + W.a₁ * x + W.a₃ with hBdef
  have hB' : B ≠ 0 := by rwa [hBdef]
  exact (s1378_preΨ₄_eq_R (W := W) hE hA hBdef).trans
    (s1378_w_mul_B_cube (W := W) hA hBdef hB').symm

/-- The evaluation identity psi_4(P) = prePsi_4(x) * psi_2(P). -/
lemma s1378_eval_four_eq {x y : F} :
    W.evalDivisionPolynomial x y 4 =
      (W.preΨ₄).eval x * (2 * y + W.a₁ * x + W.a₃) := by
  rw [WeierstrassCurve.evalDivisionPolynomial, WeierstrassCurve.ψ_four]
  simp only [Polynomial.evalEval_mul, Polynomial.evalEval_C]
  congr 1
  rw [WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.evalEval_polynomialY]

/-- **The omega identity at m = 2:**  psi_2(2P) * psi_2(P)^4 = psi_4(P) for every
point P, in every characteristic. -/
theorem s1378OmegaIdentity_two : s1378OmegaIdentity W 2 := by
  intro P
  cases P with
  | zero => simp [s1378WCoord]
  | some x y hns =>
      have hpsi2 : W.evalDivisionPolynomialAtPoint 2
          (WeierstrassCurve.Affine.Point.some x y hns) = 2 * y + W.a₁ * x + W.a₃ := by
        rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_some,
          WeierstrassCurve.evalDivisionPolynomial_two]
      by_cases hB0 : 2 * y + W.a₁ * x + W.a₃ = 0
      · rw [hpsi2, hB0]
        rw [show (2 : ℤ) * 2 = 4 by norm_num,
          WeierstrassCurve.evalDivisionPolynomialAtPoint_some, s1378_eval_four_eq, hB0]
        ring
      · have hyne : y ≠ W.toAffine.negY x y := by
          intro hy
          apply hB0
          rw [WeierstrassCurve.Affine.negY] at hy
          linear_combination hy
        let u : F := W.toAffine.addX x x (W.toAffine.slope x x y y)
        let v : F := W.toAffine.addY x x y (W.toAffine.slope x x y y)
        let h' : W.toAffine.Nonsingular u v :=
          W.toAffine.nonsingular_add hns hns fun hxy => hyne hxy.right
        have h2Peq : WeierstrassCurve.Affine.Point.some x y hns +
            WeierstrassCurve.Affine.Point.some x y hns =
              WeierstrassCurve.Affine.Point.some u v h' :=
          WeierstrassCurve.Affine.Point.add_self_of_Y_ne hyne
        have h2Pz : (2 : ℤ) • WeierstrassCurve.Affine.Point.some x y hns =
            WeierstrassCurve.Affine.Point.some u v h' := by
          rw [show (2 : ℤ) • WeierstrassCurve.Affine.Point.some x y hns =
            (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hns from natCast_zsmul _ 2,
            two_nsmul]
          exact h2Peq
        rw [h2Pz, s1378WCoord_some, hpsi2]
        rw [show (2 : ℤ) * 2 = 4 by norm_num,
          WeierstrassCurve.evalDivisionPolynomialAtPoint_some, s1378_eval_four_eq]
        have h := s1378_preΨ₄_eq_w_two_mul (W := W) hns hB0
        rw [h]
        ring

/-- **The zero criterion at n = 4, unconditionally in every characteristic.** -/
theorem divisionPolynomialZeroCriterion_four :
    W.DivisionPolynomialZeroCriterion 4 := by
  have h := s1378ZeroCriterion_two_mul_of_omega (W := W) (m := 2)
    (s1378OmegaIdentity_two W) (divisionPolynomialZeroCriterion_two W)
  rw [show (2 : ℤ) * 2 = 4 by norm_num] at h
  exact h

/-- The root half of the zero criterion at n = 4. -/
theorem divisionPolynomialRootsAreTorsion_four : W.DivisionPolynomialRootsAreTorsion 4 :=
  ((W.divisionPolynomialZeroCriterion_iff_detects 4).mp
    (divisionPolynomialZeroCriterion_four W)).2

/-- The root set of psi_4 is exactly the 4-torsion subgroup. -/
theorem rootSet_four_eq_torsion :
    {P : W.toAffine.Point | W.evalDivisionPolynomialAtPoint 4 P = 0} =
      {P : W.toAffine.Point | (4 : ℤ) • P = 0} := by
  ext P
  exact (divisionPolynomialZeroCriterion_four W P).symm

/-! ## 5. Axiom footprint -/

#print axioms s1378RootsAreTorsion_of_detection_card
#print axioms s1378RootsAreTorsion_of_detection_cardinality
#print axioms s1378ZeroCriterion_of_detection_cardinality
#print axioms s1378ZeroCriterion_of_input
#print axioms s1378WCoord_eq_zero_iff_two_zsmul
#print axioms s1378ZeroCriterion_two_mul_of_omega
#print axioms s1378RootsAreTorsion_two_mul_of_omega
#print axioms s1378_preΨ₄_eq_w_two_mul
#print axioms s1378OmegaIdentity_two
#print axioms divisionPolynomialZeroCriterion_four
#print axioms divisionPolynomialRootsAreTorsion_four
#print axioms rootSet_four_eq_torsion

end Field

end WeierstrassCurve
