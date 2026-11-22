/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S1626AddXYZSmulEvalPortActual
import tmp.sheaf.xif.paper.S1906RankTwoTorsionActual

/-!
# S1924: the division-polynomial zero criterion, via multiplication-by-n

S1906 isolated the reverse division-polynomial criterion

  S1906ZeroCriterion l :  psi_l(P) = 0  ->  (l : Z) • P = 0

as input (b) of the division-polynomial route to the rank-two basis gap,
and recorded that Mathlib v4.32.2 has no such statement for l >= 3.

This file proves the zero criterion, and in fact the full group-law criterion

  n • P = 0  <->  psi_n(P) = 0

for every field `F` with decidable equality (automatic classically), every
Weierstrass curve and every integer n.  No separability, torsion cardinality,
x-coordinate formula, divisor theory or extra hypothesis is used.

## Proof route

The key input is the universal multiplication-by-n formula already proved in
S1626 (the TauCeti universal-curve port):

  s1626ZSMulPointEqSmulEval :
    (n • P).toJacobian.point = class (phi_n(P), omega_n(P), psi_n(P)).

Its third coordinate is exactly `psi_n(P)`, i.e. the project's
`evalDivisionPolynomialAtPoint n P`.  Two elementary consequences give the
two halves of the criterion.

* Detection (torsion -> psi_n vanishes).  If n • P = 0 then the class of
  `(phi_n(P), omega_n(P), psi_n(P))` is zero, hence equivalent to
  `![1, 1, 0]`; scaling preserves the Z-coordinate, so psi_n(P) = 0.

* Reverse detection (psi_n vanishes -> torsion).  If psi_n(P) = 0, the
  evaluated triple has Z = 0.  It is nonsingular because the point class
  `(n • P).toJacobian` is nonsingular and the evaluated triple is a
  representative of that class (this uses
  `Jacobian.nonsingularLift_iff`, so no ring-level specialization of
  nonsingularity is needed).  Mathlib's `equiv_zero_of_Z_eq_zero` then
  shows that the class is the zero class, hence n • P = 0.

This is the "universal property of multiplication-by-l" route: everything
is read off from the universal polynomial identity, and no local analysis of
the divisor of psi_n is required.

## Consequences for S1906

* `S1924S1906ZeroCriterion l` inhabits `S1906ZeroCriterion l`;
* `S1924S1906Detection l` inhabits `S1906Detection l`;
* `S1924S1906Criterion l` inhabits `S1906Criterion l`.

Consequently the entire division-polynomial route of S1906 no longer needs
the x-coordinate formula (a) or the zero criterion (b).  The rank-two basis
gap is now **exactly** the root count of `prePsi_l`, equivalently the
separability of `prePsi_l`:

* `S1924S1906BasisGap_iff_rootCount`;
* `S1924S1906BasisGap_iff_separable`;
* `S1924S1906BasisGap_of_rootCount`;
* `S1924S1906BasisGap_of_separable`;
* `S1924S1906BasisGap_of_genericSeparable`.

The remaining input is exactly S1906's (c), the S1366/S1420 separability of
`prePsi_l` in characteristic zero, which is not proved here.

## Verification status

No `sorry`, no `admit`, no `axiom`, no `opaque`.  All exported theorems
are kernel-checked; their axiom footprint is the standard
`[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Jacobian
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1626AddXYZSmulEvalPortActual
open LeanFormal.IUT.XiFPaper.S1906RankTwoTorsionActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1329RankTwoTorsionBasisActual
open LeanFormal.IUT.XiFPaper.S1361DivisionCriterionActual
open LeanFormal.IUT.XiFPaper.S1366PrePsiSeparabilityFix

namespace LeanFormal.IUT.XiFPaper.S1924ZeroCriterionActual

/-! ## 1. The generic group-law criterion -/

/-- **The generic division-polynomial criterion.**

For every field `F` with decidable equality, every Weierstrass curve `W`
over `F`, every integer `n` and every point `P` of `W`, the point `P` is
`n`-torsion if and only if the `n`-division polynomial `psi_n` vanishes at
`P`.

The proof uses the universal multiplication-by-`n` formula
`s1626ZSMulPointEqSmulEval` and the two elementary Jacobian facts
`nonsingularLift_iff` and `equiv_zero_of_Z_eq_zero`. -/
theorem S1924Criterion_generic {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) (n : ℤ) :
    ∀ P : W.toAffine.Point,
      n • P = 0 ↔ W.evalDivisionPolynomialAtPoint n P = 0 := by
  intro P
  cases P with
  | zero => exact iff_of_true (zsmul_zero n) (by simp)
  | some x y hns =>
      constructor
      · -- Detection: n-torsion forces the division polynomial to vanish.
        intro hP
        have hfrom : n • Jacobian.Point.fromAffine (Affine.Point.some x y hns) = 0 := by
          have h := congrArg (Jacobian.Point.toAffineAddEquiv W.toJacobian).symm hP
          rw [map_zsmul, map_zero, Jacobian.Point.toAffineAddEquiv_symm_apply] at h
          exact h
        have hclass : (⟦s1626SmulEval W x y n⟧ : Jacobian.PointClass F) = ⟦![1, 1, 0]⟧ := by
          rw [← s1626ZSMulPointEqSmulEval W hns n, hfrom, Jacobian.Point.zero_point]
        have hthird : s1626SmulEval W x y n 2 = 0 :=
          (Jacobian.Z_eq_zero_of_equiv (Quotient.exact hclass)).mpr rfl
        simpa [s1626SmulEval, WeierstrassCurve.evalDivisionPolynomial] using hthird
      · -- Reverse detection: a zero of the division polynomial is n-torsion.
        intro hψ
        have hthird : s1626SmulEval W x y n 2 = 0 := by
          simpa [s1626SmulEval, WeierstrassCurve.evalDivisionPolynomial] using hψ
        have hns' : W.toJacobian.Nonsingular (s1626SmulEval W x y n) := by
          have hlift : W.toJacobian.NonsingularLift ⟦s1626SmulEval W x y n⟧ := by
            rw [← s1626ZSMulPointEqSmulEval W hns n]
            exact (n • Jacobian.Point.fromAffine (Affine.Point.some x y hns)).nonsingular
          exact (Jacobian.nonsingularLift_iff _).mp hlift
        have hclass : (⟦s1626SmulEval W x y n⟧ : Jacobian.PointClass F) = ⟦![1, 1, 0]⟧ :=
          Quotient.sound (Jacobian.equiv_zero_of_Z_eq_zero hns' hthird)
        have hpoint :
            (n • Jacobian.Point.fromAffine (Affine.Point.some x y hns)).point =
              (0 : W.toJacobian.Point).point := by
          rw [s1626ZSMulPointEqSmulEval W hns n, hclass, Jacobian.Point.zero_point]
        have hjac : n • Jacobian.Point.fromAffine (Affine.Point.some x y hns) = 0 :=
          Jacobian.Point.ext_iff.mpr hpoint
        have hmap := congrArg (Jacobian.Point.toAffineAddEquiv W.toJacobian) hjac
        rw [map_zsmul, map_zero] at hmap
        have hinv : (Jacobian.Point.toAffineAddEquiv W.toJacobian)
            (Jacobian.Point.fromAffine (Affine.Point.some x y hns)) =
              Affine.Point.some x y hns := by
          rw [← Jacobian.Point.toAffineAddEquiv_symm_apply]
          exact (Jacobian.Point.toAffineAddEquiv W.toJacobian).apply_symm_apply _
        rwa [hinv] at hmap

/-- S1361's forward detection statement, now unconditional for every
integer `n` and every curve. -/
theorem S1924Detection_generic {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) (n : ℤ) :
    s1361Detection W n := by
  intro P hP
  exact (S1924Criterion_generic W n P).mp hP

/-- S1361's reverse detection statement, now unconditional for every integer
`n` and every curve.  This is the generic form of S1906's (b). -/
theorem S1924ZeroCriterion_generic {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) (n : ℤ) :
    s1361ZeroCriterion W n := by
  intro P hP
  exact (S1924Criterion_generic W n P).mpr hP

/-- S1329's group-law criterion, now unconditional for every natural `l` and
every curve over an algebraically closed field. -/
theorem S1924DivisionCriterion {F : Type*} [Field F] [DecidableEq F]
    [IsAlgClosed F] (W : WeierstrassCurve.Affine F) (l : ℕ) :
    s1329DivisionCriterion W l := by
  intro P
  exact S1924Criterion_generic W (l : ℤ) P

/-! ## 2. Specialisation to the actual curve E' of S1906 -/

/-- Classical decidable equality on the algebraic closure of F'. -/
local instance S1924KDecEq : DecidableEq S1906K := Classical.decEq _

/-- **S1906's (b) is proved.**  Every zero of `psi_l` on the actual curve
E' over the algebraic closure of F' is `l`-torsion. -/
theorem S1924S1906ZeroCriterion (l : PrimeGeFive) :
    S1906ZeroCriterion l :=
  S1924ZeroCriterion_generic S1906W (l.value : ℤ)

/-- The forward detection half of the S1906 criterion, also unconditional. -/
theorem S1924S1906Detection (l : PrimeGeFive) :
    S1906Detection l :=
  S1924Detection_generic S1906W (l.value : ℤ)

/-- **The full group-law criterion for the actual E'.**  This removes both the
x-coordinate-formula input (a) and the zero-criterion input (b) from the
S1906 division-polynomial route. -/
theorem S1924S1906Criterion (l : PrimeGeFive) :
    S1906Criterion l := by
  rw [S1906Criterion_iff]
  exact ⟨S1924S1906Detection l, S1924S1906ZeroCriterion l⟩

/-! ## 3. Consumers: the basis gap is now exactly separability -/

/-- Unconditional form of S1906's exact count: the actual l-torsion has one
point at infinity plus two points over each distinct root of `prePsi_l`. -/
theorem S1924S1906NatCard_eq (l : PrimeGeFive) :
    Nat.card (S1720Curve.LTorsion l) =
      1 + 2 * (s1329RootFinset S1906W l.value).card :=
  S1906NatCard_eq l (S1924S1906Criterion l)

/-- **The rank-two basis gap is exactly the root count of `prePsi_l`.**
No x-coordinate formula and no zero criterion remain as hypotheses. -/
theorem S1924S1906BasisGap_iff_rootCount (l : PrimeGeFive) :
    S1725RankTwoBasisGap l ↔ S1906RootCount l :=
  S1906RankTwoBasisGap_iff_rootCount_of_criterion l (S1924S1906Criterion l)

/-- The root count of `prePsi_l` is equivalent to separability of
`prePsi_l` (both over the characteristic-zero closure). -/
theorem S1924S1906RootCount_iff_separable (l : PrimeGeFive) :
    S1906RootCount l ↔ S1906Separability l := by
  refine ⟨?_, S1906RootCount_of_separable l⟩
  intro h
  have hpre : S1906W.preΨ (l.value : ℤ) ≠ 0 := S1906_preΨ_ne_zero l
  have hsplit : (S1906W.preΨ (l.value : ℤ)).Splits := IsAlgClosed.splits _
  have hdeg : (S1906W.preΨ (l.value : ℤ)).natDegree = (l.value ^ 2 - 1) / 2 := by
    rw [WeierstrassCurve.natDegree_preΨ (W := S1906W) (n := (l.value : ℤ))
      (by exact_mod_cast l.prime.ne_zero)]
    rw [if_neg (S1906_not_even l)]
    simp
  have hcard : (S1906W.preΨ (l.value : ℤ)).roots.toFinset.card =
      (S1906W.preΨ (l.value : ℤ)).natDegree := by
    unfold S1906RootCount s1329RootFinset at h
    rw [h, hdeg]
  have hnodup : (S1906W.preΨ (l.value : ℤ)).roots.Nodup := by
    rw [← Multiset.toFinset_card_eq_card_iff_nodup, hcard, hdeg,
      ← hsplit.natDegree_eq_card_roots, hdeg]
  exact (Polynomial.nodup_roots_iff_of_splits hpre hsplit).mp hnodup

/-- **The rank-two basis gap is exactly separability of `prePsi_l`.**
This is the sharp form of the remaining S1906 input after the zero criterion
is removed. -/
theorem S1924S1906BasisGap_iff_separable (l : PrimeGeFive) :
    S1725RankTwoBasisGap l ↔ S1906Separability l :=
  (S1924S1906BasisGap_iff_rootCount l).trans
    (S1924S1906RootCount_iff_separable l)

/-- The basis gap follows from the root count of `prePsi_l`. -/
theorem S1924S1906BasisGap_of_rootCount (l : PrimeGeFive)
    (h : S1906RootCount l) : S1725RankTwoBasisGap l :=
  (S1924S1906BasisGap_iff_rootCount l).mpr h

/-- The basis gap follows from separability of `prePsi_l`. -/
theorem S1924S1906BasisGap_of_separable (l : PrimeGeFive)
    (hsep : S1906Separability l) : S1725RankTwoBasisGap l :=
  (S1924S1906BasisGap_iff_separable l).mpr hsep

/-- The basis gap follows from the tree's generic separability input
S1366GenericOddPrePsiSeparableInput. -/
theorem S1924S1906BasisGap_of_genericSeparable
    (h : S1366GenericOddPreΨSeparableInput) (l : PrimeGeFive) :
    S1725RankTwoBasisGap l :=
  S1924S1906BasisGap_of_rootCount l
    (S1906RootCount_of_genericPreΨSeparable h l)

/-- The exact cardinality S1906ExactFirstMissing follows from separability. -/
theorem S1924S1906NatCard_eq_sq_of_separable (l : PrimeGeFive)
    (hsep : S1906Separability l) :
    Nat.card (S1720Curve.LTorsion l) = l.value ^ 2 :=
  (S1906RankTwoBasisGap_iff_natCard l).mp
    (S1924S1906BasisGap_of_separable l hsep)

/-- The torsion-cardinality form and separability are equivalent. -/
theorem S1924S1906TorsionCardinality_iff_separable (l : PrimeGeFive) :
    S1906TorsionCardinality l ↔ S1906Separability l := by
  rw [S1906TorsionCardinality_iff_basisGap, S1924S1906BasisGap_iff_separable]

/-! ## 4. Axiom footprint -/

#print axioms S1924Criterion_generic
#print axioms S1924Detection_generic
#print axioms S1924ZeroCriterion_generic
#print axioms S1924DivisionCriterion
#print axioms S1924S1906ZeroCriterion
#print axioms S1924S1906Detection
#print axioms S1924S1906Criterion
#print axioms S1924S1906NatCard_eq
#print axioms S1924S1906BasisGap_iff_rootCount
#print axioms S1924S1906RootCount_iff_separable
#print axioms S1924S1906BasisGap_iff_separable
#print axioms S1924S1906BasisGap_of_rootCount
#print axioms S1924S1906BasisGap_of_separable
#print axioms S1924S1906BasisGap_of_genericSeparable
#print axioms S1924S1906NatCard_eq_sq_of_separable
#print axioms S1924S1906TorsionCardinality_iff_separable

end LeanFormal.IUT.XiFPaper.S1924ZeroCriterionActual
