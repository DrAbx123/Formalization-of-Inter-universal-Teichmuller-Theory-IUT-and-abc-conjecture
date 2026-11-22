/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/

import tmp.sheaf.xif.paper.S2480CycleTypeRepairActual
import tmp.sheaf.xif.paper.S2442QE5DegreeOrderSubagentActual
import tmp.sheaf.xif.paper.S2009DicksonActual
import tmp.sheaf.xif.paper.S2253LinearDisjointActual
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.CharP
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing

/-!
# S2492: refutation search for the actual (10, 2) cycle-type input

The D5 chain of S2480/S2485 reduces the missing large-image input to

  S2480FirstMissing
  = there is an actual sigma : Gal(Fbar/F') whose mod-5 matrix acts on the
    twelve pairs {+P} of nonzero 5-torsion points with cycle type (10, 2).

This file searches for a refutation of that proposition.  The mathematical
outcome is negative: no unconditional refutation is found, and the actual
arithmetic points in the opposite direction.  The file records the precise
obstructions that remain, with no fake inhabitant of any missing proposition.

## What is actually proved here

1. S2492_matrix_sq_eq: the Cayley--Hamilton identity for a 2 x 2 matrix over
   F_5, A * A = trace(A) * A - det(A) * 1.
2. S2492_pairPermHom_NegOne: the central scalar -I acts trivially on the
   twelve pairs, so pairPermHom (-I) = 1.
3. S2492_det_ne_one_of_pairCycle102: a matrix whose pair permutation has
   cycle type (10, 2) cannot have determinant 1.  This is the finite-group
   obstruction: if the determinant is trivial, then the mod-5 image lies in
   SL_2(F_5) and the projective image in A_5, which has no element of
   order 10.
4. Consequently, if every element of the actual range has determinant one
   (S2492AllDetOne / S2492RangeLeSL2), then S2480FirstMissing is false.
5. Conversely, if the actual range is all of GL_2(F_5) (in particular, at
   the fixed basis S1982Basis), then S2480FirstMissing is true, because
   the explicit S2009 matrix g102 = !![0, 1; 1, 1] has pair cycle type
   (10, 2).
6. The two candidate arithmetic/bridge inputs are named, not assumed:
   * S2492DetOneLink: if F' contains a primitive fifth root of unity, then
     the mod-5 determinant is trivial (Weil pairing / cyclotomic character).
     This is the only route by which the determinant obstruction could apply.
   * S2492FullRangeTransfer: the S2442 projective bridge
     Gal(psi_5/Q) ~= GL_2(F_5)/{+-I}, the S2253 linear disjointness of F'
     with the psi_5 splitting field, and the S1987 full-image finite
     computation together force the mod-5 range over F' to be the full
     GL_2(F_5).  (The S2253 field is the x-coordinate/psi_5 field; passing
     to the full 5-division field is part of the transfer package.)
   No inhabitant of either proposition is produced here.

## Why this is a refutation search, not a refutation

The actual field F' = SplittingField(S1687H * (X^2 + 1)) contains i and
sqrt(-3) (S1720HasSqrtNegOne, S1725ExistsSqrtNegThree), hence contains
Q(zeta_12).  Its quadratic subfields are Q(i), Q(sqrt(-3)) and
Q(sqrt(3)); the only quadratic subfield of the 5-division field is
Q(sqrt(5)).  Thus F' cap Q(E[5]) = Q and the mod-5 image over F' is the
same as over Q, namely GL_2(F_5) by the S1987 finite computation.  In
particular F' does not contain zeta_5 (its Galois group has no cyclic
quartic quotient), so the determinant obstruction is not available.  This
arithmetic verification is recorded in
coord/reports/S1987-d5-large-image-five-actual.md; it is not formalized here.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2492RefutationSearchActual

open Matrix
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S2480CycleTypeRepairActual
open LeanFormal.IUT.XiFPaper.S2442QE5DegreeOrderSubagentActual
open LeanFormal.IUT.XiFPaper.S2253LinearDisjointActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual

abbrev S2492GL2 : Type := GL (Fin 2) (ZMod 5)

/-! ## 1. The finite group obstruction: determinant one is impossible -/

/-- The Cayley--Hamilton identity for a 2 x 2 matrix over F_5. -/
theorem S2492_matrix_sq_eq (A : Matrix (Fin 2) (Fin 2) (ZMod 5)) :
    A * A = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.trace_fin_two, Matrix.det_fin_two,
      Fin.sum_univ_two] <;> ring

/-- The central involution -I of GL_2(F_5), realized as a scalar unit. -/
noncomputable def S2492NegOne : S2492GL2 :=
  Matrix.GeneralLinearGroup.scalar (Fin 2)
    (Units.mk0 (-1 : ZMod 5) (by norm_num))

/-- The underlying matrix of S2492NegOne is -1. -/
theorem S2492NegOne_val :
    (S2492NegOne : Matrix (Fin 2) (Fin 2) (ZMod 5)) = -1 := by
  rw [S2492NegOne, Matrix.GeneralLinearGroup.coe_scalar]
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.scalar_apply, Units.val_mk0]
  · simp [Matrix.scalar_apply, h]

/-- -I acts trivially on the twelve pairs {+v}. -/
theorem S2492_pairPermHom_NegOne :
    pairPermHom S2492NegOne = 1 := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  show normalize (S2492NegOne • x.1) = x.1
  have hneg : (S2492NegOne • x.1) = -x.1 := by
    ext i
    fin_cases i <;>
      simp [S2492NegOne_val, Units.smul_def, Matrix.smul_eq_mulVec,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  rw [hneg, normalize_neg, normalize_of_isRep x.1 x.2]

/-- A matrix whose pair permutation has cycle type (10, 2) has determinant
different from one.  This is the exact finite obstruction for an image
contained in SL_2(F_5). -/
theorem S2492_det_ne_one_of_pairCycle102
    (g : S2492GL2)
    (hc : (pairPermHom g).cycleType = ({10, 2} : Multiset Nat)) :
    Matrix.GeneralLinearGroup.det g ≠ 1 := by
  intro hdet
  have horder : orderOf (pairPermHom g) = 10 := by
    rw [← Equiv.Perm.lcm_cycleType, hc]
    decide
  let A : Matrix (Fin 2) (Fin 2) (ZMod 5) := (g : Matrix (Fin 2) (Fin 2) (ZMod 5))
  have hdetA : A.det = 1 := by
    have h := congrArg Units.val hdet
    simpa [A, Matrix.GeneralLinearGroup.val_det_apply] using h
  have hCH : A * A = A.trace • A - (1 : ZMod 5) • (1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) := by
    simpa [hdetA] using S2492_matrix_sq_eq A
  have hneg := S2492_pairPermHom_NegOne
  have hcases : ∀ c : ZMod 5, c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by
    decide
  rcases hcases A.trace with h0 | h1 | h2 | h3 | h4
  · -- trace 0: A^2 = -1
    have hA2 : A * A = -1 := by
      rw [hCH, h0]
      simp
    have hg2 : g ^ 2 = S2492NegOne := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      have h := congrFun (congrFun hA2 i) j
      simpa [A, S2492NegOne_val, pow_two, Units.val_pow_eq_pow_val] using h
    have hp2 : pairPermHom g ^ 2 = 1 := by
      rw [← map_pow, hg2, hneg]
    have hdvd : orderOf (pairPermHom g) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr hp2
    rw [horder] at hdvd
    exact (by norm_num : ¬ (10 ∣ 2)) hdvd
  · -- trace 1: A^3 = -1
    have hA2 : A * A = A - 1 := by
      rw [hCH, h1]
      simp
    have hA3 : A ^ 3 = -1 := by
      calc
        A ^ 3 = A ^ 2 * A := by rw [pow_succ]
        _ = (A - 1) * A := by rw [pow_two, hA2]
        _ = A * A - A := by rw [sub_mul, one_mul]
        _ = (A - 1) - A := by rw [hA2]
        _ = -1 := by abel
    have hg3 : g ^ 3 = S2492NegOne := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      have h := congrFun (congrFun hA3 i) j
      simpa [A, S2492NegOne_val, Units.val_pow_eq_pow_val] using h
    have hp3 : pairPermHom g ^ 3 = 1 := by
      rw [← map_pow, hg3, hneg]
    have hdvd : orderOf (pairPermHom g) ∣ 3 :=
      orderOf_dvd_iff_pow_eq_one.mpr hp3
    rw [horder] at hdvd
    exact (by norm_num : ¬ (10 ∣ 3)) hdvd
  · -- trace 2: (A - 1)^2 = 0 and A^5 = 1
    have hA2 : A * A = A + A - 1 := by
      rw [hCH, h2]
      simp [two_smul]
    have hsq : (A - 1) * (A - 1) = 0 := by
      rw [show (A - 1) * (A - 1) = A * A - A - A + 1 by noncomm_ring]
      rw [hA2]
      abel
    have hpow : (A - 1) ^ 5 = 0 := by
      have h := pow_add (A - 1) 2 3
      rw [show 2 + 3 = 5 by norm_num] at h
      rw [h, hsq, zero_mul]
    have hsub : (A - 1) ^ 5 = A ^ 5 - 1 := by
      simpa using (sub_pow_char_of_commute (p := 5) (x := A)
        (y := (1 : Matrix (Fin 2) (Fin 2) (ZMod 5)))
        (Commute.one_right A))
    have hA5 : A ^ 5 = 1 := by
      rw [hsub] at hpow
      exact sub_eq_zero.mp hpow
    have hg5 : g ^ 5 = 1 := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      have h := congrFun (congrFun hA5 i) j
      simpa [A, Units.val_pow_eq_pow_val] using h
    have hp5 : pairPermHom g ^ 5 = 1 := by
      rw [← map_pow, hg5, map_one]
    have hdvd : orderOf (pairPermHom g) ∣ 5 :=
      orderOf_dvd_iff_pow_eq_one.mpr hp5
    rw [horder] at hdvd
    exact (by norm_num : ¬ (10 ∣ 5)) hdvd
  · -- trace 3: (A + 1)^2 = 0 and A^5 = -1
    have h3A : (3 : ZMod 5) • A = A + A + A := by
      calc
        (3 : ZMod 5) • A = (1 + 1 + 1 : ZMod 5) • A := by
          simp [show (3 : ZMod 5) = 1 + 1 + 1 by norm_num]
        _ = A + A + A := by simp [add_smul]
    have hA2 : A * A = A + A + A - 1 := by
      have h := hCH
      rw [h3, h3A] at h
      simpa using h
    have h5A : (5 : Nat) • A = 0 := by
      rw [nsmul_eq_mul,
        show (5 : Matrix (Fin 2) (Fin 2) (ZMod 5)) = 0 from
          CharP.cast_eq_zero (R := Matrix (Fin 2) (Fin 2) (ZMod 5)) 5,
        zero_mul]
    have hsq : (A + 1) * (A + 1) = 0 := by
      have hsum : A * A + A + A + 1 = 0 := by
        rw [hA2]
        have hfive : (A + A + A - 1) + A + A + 1 = (5 : Nat) • A := by
          abel
        rw [hfive, h5A]
      rw [show (A + 1) * (A + 1) = A * A + A + A + 1 by noncomm_ring]
      exact hsum
    have hpow : (A + 1) ^ 5 = 0 := by
      have h := pow_add (A + 1) 2 3
      rw [show 2 + 3 = 5 by norm_num] at h
      rw [h, hsq, zero_mul]
    have hsub : (A + 1) ^ 5 = A ^ 5 + 1 := by
      simpa using (add_pow_char_of_commute (p := 5) (x := A)
        (y := (1 : Matrix (Fin 2) (Fin 2) (ZMod 5)))
        (Commute.one_right A))
    have hA5 : A ^ 5 = -1 := by
      rw [hsub] at hpow
      exact eq_neg_of_add_eq_zero_left hpow
    have hg5 : g ^ 5 = S2492NegOne := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      have h := congrFun (congrFun hA5 i) j
      simpa [A, S2492NegOne_val, Units.val_pow_eq_pow_val] using h
    have hp5 : pairPermHom g ^ 5 = 1 := by
      rw [← map_pow, hg5, hneg]
    have hdvd : orderOf (pairPermHom g) ∣ 5 :=
      orderOf_dvd_iff_pow_eq_one.mpr hp5
    rw [horder] at hdvd
    exact (by norm_num : ¬ (10 ∣ 5)) hdvd
  · -- trace 4 = -1: A^3 = 1
    have h4A : (4 : ZMod 5) • A = -A := by
      simpa [show (4 : ZMod 5) = -1 by norm_num] using
        (neg_one_smul (R := ZMod 5) A)
    have hA2 : A * A = -A - 1 := by
      have h := hCH
      rw [h4, h4A] at h
      simpa using h
    have hpoly : A ^ 2 + A + 1 = 0 := by
      rw [pow_two, hA2]
      abel
    have hA3 : A ^ 3 = 1 := by
      have hmul : (A ^ 2 + A + 1) * (A - 1) = 0 := by
        rw [hpoly, zero_mul]
      have hident : (A ^ 2 + A + 1) * (A - 1) = A ^ 3 - 1 := by
        noncomm_ring
      rw [hident] at hmul
      exact sub_eq_zero.mp hmul
    have hg3 : g ^ 3 = 1 := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      have h := congrFun (congrFun hA3 i) j
      simpa [A, Units.val_pow_eq_pow_val] using h
    have hp3 : pairPermHom g ^ 3 = 1 := by
      rw [← map_pow, hg3, map_one]
    have hdvd : orderOf (pairPermHom g) ∣ 3 :=
      orderOf_dvd_iff_pow_eq_one.mpr hp3
    rw [horder] at hdvd
    exact (by norm_num : ¬ (10 ∣ 3)) hdvd

/-! ## 2. The actual range and the two directions -/

/-- The actual range of the mod-5 matrix representation at a basis. -/
abbrev S2492Range (b : S1725TorsionBasis S1987Five) : Subgroup
    (GL (Fin 2) (ZMod S1987Five.value)) :=
  (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range

/-- The determinant obstruction on the actual range: every matrix in the
range has determinant one.  This is the exact hypothesis under which
S2480FirstMissing is refuted by the finite group theorem above. -/
def S2492RangeLeSL2 (b : S1725TorsionBasis S1987Five) : Prop :=
  ∀ g ∈ S2492Range b,
    Matrix.GeneralLinearGroup.det g = 1

/-- The pointwise form of the determinant obstruction. -/
def S2492AllDetOne : Prop :=
  ∀ σ : S1725AbsoluteGalois,
    Matrix.GeneralLinearGroup.det
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis σ) = 1

/-- Pointwise determinant one implies the range form. -/
theorem S2492RangeLeSL2_of_allDetOne (h : S2492AllDetOne) :
    S2492RangeLeSL2 S1982Basis := by
  rintro g ⟨σ, rfl⟩
  exact h σ

/-- The refutation under a trivial determinant.  If the actual mod-5
image is contained in SL_2(F_5), then no actual Galois element has pair
cycle type (10, 2). -/
theorem S2492NotFirstMissing_of_rangeLeSL2
    (hSL : S2492RangeLeSL2 S1982Basis) :
    ¬ S2480FirstMissing := by
  rintro ⟨σ, hσ⟩
  let g : GL (Fin 2) (ZMod S1987Five.value) :=
    S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis σ
  have hmem : g ∈ S2492Range S1982Basis := ⟨σ, rfl⟩
  have hdet : Matrix.GeneralLinearGroup.det g = 1 := hSL g hmem
  exact S2492_det_ne_one_of_pairCycle102 g hσ hdet

/-- The same refutation from the pointwise determinant hypothesis. -/
theorem S2492NotFirstMissing_of_allDetOne
    (h : S2492AllDetOne) : ¬ S2480FirstMissing :=
  S2492NotFirstMissing_of_rangeLeSL2 (S2492RangeLeSL2_of_allDetOne h)

/-- Conversely, S2480FirstMissing forces some actual matrix in the range to
have determinant different from one.  This is the unconditional consequence
of the finite obstruction. -/
theorem S2492FirstMissing_det_ne_one
    (h : S2480FirstMissing) :
    ∃ σ : S1725AbsoluteGalois,
      Matrix.GeneralLinearGroup.det
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis σ) ≠ 1 := by
  rcases h with ⟨σ, hσ⟩
  exact ⟨σ, S2492_det_ne_one_of_pairCycle102 _ hσ⟩

/-- The pointwise determinant-one hypothesis is incompatible with
S2480FirstMissing. -/
theorem S2492not_allDetOne_of_firstMissing
    (h : S2480FirstMissing) : ¬ S2492AllDetOne :=
  fun hAll => S2492NotFirstMissing_of_allDetOne hAll h

/-- The range determinant-one hypothesis is incompatible with
S2480FirstMissing. -/
theorem S2492not_rangeLeSL2_of_firstMissing
    (h : S2480FirstMissing) : ¬ S2492RangeLeSL2 S1982Basis :=
  fun hSL => S2492NotFirstMissing_of_rangeLeSL2 hSL h

/-- If the explicit S2009 element g102 lies in the actual range, then the
actual (10, 2) element exists. -/
theorem S2492FirstMissing_of_mem_g102
    (h : g102 ∈ S2492Range S1982Basis) :
    S2480FirstMissing := by
  obtain ⟨σ, hσ⟩ := MonoidHom.mem_range.mp h
  refine ⟨σ, ?_⟩
  rw [hσ]
  exact cycleType_pairPerm_g102

/-- The positive direction.  Full mod-5 range at the fixed basis gives the
actual (10, 2) element, hence S2480FirstMissing. -/
theorem S2492FirstMissing_of_rangeTop
    (h : S2492Range S1982Basis = ⊤) :
    S2480FirstMissing :=
  S2492FirstMissing_of_mem_g102 (by
    rw [h]
    exact Subgroup.mem_top g102)

/-- A full range would refute every attempt to refute S2480FirstMissing. -/
theorem S2492NotNotFirstMissing_of_rangeTop
    (h : S2492Range S1982Basis = ⊤) :
    ¬ ¬ S2480FirstMissing :=
  fun hnot => hnot (S2492FirstMissing_of_rangeTop h)

/-! ## 3. The precise arithmetic obstruction candidates

The two propositions below are the exact inputs that would turn the search
into a proof or a refutation.  They are definitions, not axioms; no inhabitant
is asserted. -/

/-- The arithmetic condition that would make the determinant obstruction
applicable: F' contains a primitive fifth root of unity.  Under the Weil
pairing the determinant of the mod-5 representation is the cyclotomic
character, so this condition is equivalent to the determinant being trivial
on the whole absolute Galois group. -/
def S2492ZetaFiveInF' : Prop :=
  ∃ ζ : S1720Field, ζ ^ 5 = 1 ∧ ζ ≠ 1

/-- The exact missing link from the arithmetic condition to the determinant
obstruction: if F' contains zeta_5, then the mod-5 determinant is trivial.
This is the Weil-pairing/cyclotomic-character step, not formalized in the
tree. -/
def S2492DetOneLink : Prop :=
  S2492ZetaFiveInF' → S2492AllDetOne

/-- Conditional refutation: under zeta_5 in F' and the determinant link, the
actual (10, 2) element does not exist. -/
theorem S2492NotFirstMissing_of_zetaFive
    (hζ : S2492ZetaFiveInF')
    (hlink : S2492DetOneLink) :
    ¬ S2480FirstMissing :=
  S2492NotFirstMissing_of_allDetOne (hlink hζ)

/-- The exact missing transfer in the positive direction: the S2442
projective bridge for psi_5, the S2253 linear disjointness of F' with the
psi_5 splitting field, and the S1987 full-image finite computation together
force the actual mod-5 range over F' to be the full GL_2(F_5).  This
packages the pair-action/x-coordinate bridge, the passage from the psi_5
field to the full 5-division field, and the Dedekind--Frobenius/
finite-computation input of S1987. -/
def S2492FullRangeTransfer : Prop :=
  s2253IntersectionIsBot →
    S2442Psi5ProjectiveBridgeRequired →
      S2492Range S1982Basis = ⊤

/-- Conditional positive direction: if the linear-disjointness and the
projective bridge are available, together with the exact transfer above, then
S2480FirstMissing is true.  This is the mathematical reason why the
refutation search fails: the actual arithmetic points to the full image. -/
theorem S2492FirstMissing_of_disjointness
    (hdisj : s2253IntersectionIsBot)
    (hbridge : S2442Psi5ProjectiveBridgeRequired)
    (htransfer : S2492FullRangeTransfer) :
    S2480FirstMissing :=
  S2492FirstMissing_of_rangeTop (htransfer hdisj hbridge)

/-- The determinant refutation route, isolated.  It needs zeta_5 in F'
and the Weil-pairing determinant link; the actual field data (see the header)
makes zeta_5 in F' false, so this route is expected to be unavailable. -/
def S2492RefutationRoute : Prop :=
  S2492ZetaFiveInF' ∧ S2492DetOneLink

/-- The exact missing input of the positive route (the route that the actual
arithmetic supports): the S2253 disjointness, the S2442 bridge, and the
transfer to full range.  No inhabitant is asserted. -/
def S2492ExactMissing : Prop :=
  s2253IntersectionIsBot ∧ S2442Psi5ProjectiveBridgeRequired ∧
    S2492FullRangeTransfer

/-! ## 4. Axiom footprint -/

#print axioms S2492_matrix_sq_eq
#print axioms S2492_pairPermHom_NegOne
#print axioms S2492_det_ne_one_of_pairCycle102
#print axioms S2492NotFirstMissing_of_rangeLeSL2
#print axioms S2492FirstMissing_det_ne_one
#print axioms S2492not_allDetOne_of_firstMissing
#print axioms S2492not_rangeLeSL2_of_firstMissing
#print axioms S2492FirstMissing_of_mem_g102
#print axioms S2492FirstMissing_of_rangeTop
#print axioms S2492NotFirstMissing_of_zetaFive
#print axioms S2492FirstMissing_of_disjointness

end LeanFormal.IUT.XiFPaper.S2492RefutationSearchActual

end
