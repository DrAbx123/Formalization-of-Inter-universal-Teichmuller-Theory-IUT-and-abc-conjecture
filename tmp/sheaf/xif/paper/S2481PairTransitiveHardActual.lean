/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import tmp.sheaf.xif.paper.S2440RangePairTransitiveSubagentActual
import tmp.sheaf.xif.paper.S2132D5FactorizationActual

/-!
# S2481: hard-attempt report on the actual mod-5 range pair-transitivity target

The target is the actual proposition

  S2203RangePairTransitiveRequired S1982Basis
    = PairTransitive (range (galoisLTorsionMatrixRepresentation S1987Five S1982Basis))

of the paper's D5 large-image input.

## Outcome of the attempt: BLOCKED, with the exact gap isolated

Route (ii) through S2440 needs

(a) a residue-degree-one prime of F' at which a monic integral model of a
    nonzero multiple of psi_5 has irreducible degree-twelve reduction, and
(b) the transport of the Dedekind--Frobenius root cycle type to the actual
    matrix range (S2470RootToRangeTransport).

Neither is produced here.  The finite part of (a) at 613 was verified
numerically for this attempt but is not formalized (recorded below as the plain
Prop S2481ResidueCertificate).

What is proved unconditionally here:

* S2481HZ_map_rat: the expanded integer model S2481HZ of S1720H maps to
  S1720H over Q, so reducing S2481HZ modulo 613 is exactly reducing the
  defining polynomial of F' = SplittingField S1720H at 613;
* S2481HMod613_splits: S2481HZ splits completely modulo 613, with the eight
  distinct roots 35, 226, 233, 304, 309, 380, 387, 578.  By the
  Dedekind--Frobenius theorem this means that 613 has a prime of residue degree
  one in F';
* S2481Target_of_twelveCycle: the actual target follows from the S2440
  twelve-cycle input.

No sorry, axiom, True/PUnit gate or native_decide is used.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2481PairTransitiveHardActual

open Polynomial
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual

local instance : Fact (Nat.Prime 613) := ⟨by norm_num⟩

/-! ## 1. The source polynomial modulo 613 -/

/-- The expanded integer model of S1720H = S1687H * (X^2+1). -/
def S2481HZ : ℤ[X] :=
  C 6153500390625 + C 8144985830625 * X ^ 2 + C 5965437485056 * X ^ 4 +
    C 4437808513024 * X ^ 6 + C 463856467968 * X ^ 8

/-- The reduction of the integer model modulo 613. -/
def S2481H613 : (ZMod 613)[X] :=
  C 268 + C 227 * X ^ 2 + C 380 * X ^ 4 + C 392 * X ^ 6 + C 584 * X ^ 8

/-- The integer model maps to the actual defining polynomial of F' over Q. -/
lemma S2481HZ_map_rat : S2481HZ.map (Int.castRingHom ℚ) = S1720H := by
  ext n
  by_cases hn : n ≤ 8
  · interval_cases n <;>
      (simp [S2481HZ, S1720H, S1687H, S1720SqrtPolynomial,
        Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_C,
        Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
       <;> norm_num)
  · have h1 : (S2481HZ.map (Int.castRingHom ℚ)).coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have hle : (S2481HZ.map (Int.castRingHom ℚ)).natDegree ≤ S2481HZ.natDegree :=
        Polynomial.natDegree_map_le
      have h8 : S2481HZ.natDegree = 8 := by
        unfold S2481HZ
        compute_degree!
      omega
    have h2 : S1720H.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h8 : S1720H.natDegree = 8 := by
        unfold S1720H S1687H S1720SqrtPolynomial
        compute_degree!
      omega
    rw [h1, h2]

lemma S2481HZ_mod : S2481HZ.map (Int.castRingHom (ZMod 613)) = S2481H613 := by
  ext n
  by_cases hn : n ≤ 8
  · interval_cases n <;>
      (simp [S2481HZ, S2481H613, Polynomial.coeff_add, Polynomial.coeff_C,
        Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · have h1 : (S2481HZ.map (Int.castRingHom (ZMod 613))).coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have hle : (S2481HZ.map (Int.castRingHom (ZMod 613))).natDegree ≤ S2481HZ.natDegree :=
        Polynomial.natDegree_map_le
      have h8 : S2481HZ.natDegree = 8 := by
        unfold S2481HZ
        compute_degree!
      omega
    have h2 : S2481H613.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h8 : S2481H613.natDegree = 8 := by
        unfold S2481H613
        compute_degree!
      omega
    rw [h1, h2]

lemma S2481H613_natDegree : S2481H613.natDegree = 8 := by
  unfold S2481H613
  compute_degree!

lemma S2481H613_ne_zero : S2481H613 ≠ 0 := by
  intro h
  have hd := S2481H613_natDegree
  rw [h] at hd
  simp at hd

lemma S2481H613_roots :
    ∀ r : ZMod 613, r ∈ ({35, 226, 233, 304, 309, 380, 387, 578} : Finset (ZMod 613)) →
      S2481H613.IsRoot r := by
  intro r hr
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp [Polynomial.IsRoot, S2481H613] <;> decide)

lemma S2481H613_roots_card : S2481H613.roots.card = 8 := by
  have hcard : ({35, 226, 233, 304, 309, 380, 387, 578} : Finset (ZMod 613)).card = 8 := by
    decide
  have hsub : ({35, 226, 233, 304, 309, 380, 387, 578} : Finset (ZMod 613)) ⊆
      S2481H613.roots.toFinset := by
    intro r hr
    rw [Multiset.mem_toFinset, Polynomial.mem_roots S2481H613_ne_zero]
    exact S2481H613_roots r hr
  have h1 : 8 ≤ S2481H613.roots.toFinset.card := by
    rw [← hcard]
    exact Finset.card_le_card hsub
  have h2 : S2481H613.roots.toFinset.card ≤ S2481H613.roots.card :=
    Multiset.toFinset_card_le _
  have h3 : S2481H613.roots.card ≤ S2481H613.natDegree := Polynomial.card_roots' _
  rw [S2481H613_natDegree] at h3
  omega

/-- **The source field splits completely at 613**: the integer model of its
defining polynomial has eight distinct roots modulo 613. -/
theorem S2481HMod613_splits :
    (S2481HZ.map (Int.castRingHom (ZMod 613))).Splits := by
  rw [S2481HZ_mod, Polynomial.splits_iff_card_roots, S2481H613_roots_card,
    S2481H613_natDegree]

/-! ## 2. The target and the S2440 reduction -/

/-- The actual target: pair transitivity of the actual mod-5 range at
S1982Basis. -/
def S2481Target : Prop :=
  LeanFormal.IUT.XiFPaper.S2203D5RangeActual.S2203RangePairTransitiveRequired
    LeanFormal.IUT.XiFPaper.S1982D5FiveActual.S1982Basis

/-- The target is definitionally the S2375 exact first missing. -/
theorem S2481Target_iff_S2375 : S2481Target ↔
    LeanFormal.IUT.XiFPaper.S2375RangePairTransitiveActual.S2375ExactFirstMissing :=
  Iff.rfl

/-- **The twelve-cycle input implies the actual target** (S2440). -/
theorem S2481Target_of_twelveCycle
    (h : LeanFormal.IUT.XiFPaper.S2440RangePairTransitiveSubagentActual.S2440TwelveCycleInputRequired) :
    S2481Target :=
  LeanFormal.IUT.XiFPaper.S2440RangePairTransitiveSubagentActual.S2440RangePairTransitive_of_twelveCycle h

/-- The finite-field certificate needed by the residue-data route: the integer
model of 2^36 * prePsi_5 is irreducible modulo 613.  This finite computation was
verified numerically for this attempt but is not formalized; it is a plain Prop
with no inhabitant. -/
def S2481ResidueCertificate : Prop :=
  Irreducible (S2132Psi5Z.map (Int.castRingHom (ZMod 613)))

/-! ## 3. Axiom footprint -/

#print axioms S2481HZ_map_rat
#print axioms S2481HZ_mod
#print axioms S2481HMod613_splits
#print axioms S2481Target_iff_S2375
#print axioms S2481Target_of_twelveCycle

end LeanFormal.IUT.XiFPaper.S2481PairTransitiveHardActual

end
