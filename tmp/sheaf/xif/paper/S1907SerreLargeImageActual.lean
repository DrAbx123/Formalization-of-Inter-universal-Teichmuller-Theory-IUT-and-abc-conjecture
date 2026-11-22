/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/

import tmp.sheaf.xif.paper.S1894D5LargeImageActual
import Mathlib.Data.Set.Finite.Lattice

/-!
# S1907: the Serre large-image statement on the actual curve E'/F' (S1720)

## Question

S1894 reduced the D5 remainder on the actual curve

  E' = S1667Punctured.baseChange F',   F' = SplittingField (S1687H * (X^2 + 1))

to the frozen statement

  SerreStyleLargeImageStatement S1720Curve l

(SL_2(F_l) <= im rho_{E',l} for a rank-two basis of E'[l]), and asked
whether the statement can be proved from tree-internal material or from a
known/ported Serre open-image formalization.

## Answer: MISSING, and no port currently exists

1. Tree-internal: SerreStyleLargeImageStatement and
   RankTwoTorsionBasisGap occur in LeanFormal only as definitions,
   docstrings and audit records, never as a proved conclusion.  The audit
   card IUT-I.elliptic-l-torsion-large-image
   (LeanFormal/IUT/Foundations/Geometry/EllipticTorsion.lean) is pending,
   and the local Tate input needed by the source route is the pending card
   Foundations.Geometry.elliptic-tate-uniformization
   (LeanFormal/IUT/Foundations/NumberField/LocalQParameter.lean).  The tree
   has the mod-l torsion representation and its matrix model
   (galoisLTorsionMatrixRepresentation), and a concrete pro-2 Tate-module
   example for y^2 = x^3 - x (Example36TateGaloisAction.lean), but no
   general pro-l Tate module for l >= 5, no inertia/unipotent computation
   at the multiplicative place, no Faltings height, no moduli stack, and no
   open-image theorem.  The tree's own Cor312ToABCCards.lean note lists the
   missing moduli stack (Mell)_Q, compactly bounded sets K_V and exceptional
   sets.

2. Mathlib (v4.32.2): Mathlib.AlgebraicGeometry.EllipticCurve contains
   Weierstrass curves, division polynomials and torsion points, but no
   TateModule, no Galois representation of an elliptic curve over a number
   field, no FaltingsHeight, no local height and no Serre open-image
   theorem.  A case-insensitive search of Mathlib for "open image",
   "OpenImage", "TateModule", "GaloisRepresentation" and "Faltings" returns
   only unrelated notions (open embeddings, Serre classes, etc.).

3. External Lean developments: TauCeti has
   TauCeti/AlgebraicGeometry/EllipticCurve/TateModule/ (Tate module,
   Serre's local lemma, potential good reduction) but no global open-image
   theorem and no SL_2-image statement.  The vendored IUT ports
   (tmp/external/Takkun-IUT_LEAN, tmp/external/promachina-iut-lean,
   tmp/external/iut4-sec1) contain only the same source-hypothesis shapes.
   A web search found no Lean formalization of Serre's open image theorem.
   Hence there is no external port that proves the target.

## The exact first missing

The uniform form (all l >= 5) decomposes exactly into two inputs, and both
are absent:

* S1907FirstMissing -- the cofinite Serre statement: only finitely many
  primes l >= 5 fail SL_2(F_l) <= im rho_{E',l}.  This is the standard
  corollary of Serre's open image theorem (Serre 1972, Chapter IV,
  Sections 3.2/3.4) applied to the non-CM curve E'/F', together with
  Dickson's classification of the subgroups of GL_2(F_l) (or, equivalently,
  the elementary open-subgroup argument for GL_2(Z_l)).  E' is non-CM
  because its j-invariant is the rational non-integer
  27721^3 / (16 * 3^6 * 5^6 * 7^2), while every rational CM j-invariant is
  an integer; this argument is not formalized in the tree, and the non-CM
  hypothesis remains part of the external theorem.  The effective
  source form is [GenEll] Theorem 3.8 (Mochizuki, Arithmetic elliptic curves
  in general position), which gives an explicit threshold under the extra
  hypotheses that E' is outside the finite exceptional set Exc, that l is
  at least 23040 * 100^d * (ht_Falt(E') + C d^epsilon), and (in the other
  alternative) that E' lies in a compactly bounded subset with l prime to
  the local heights and to 30.

  In particular [GenEll] Theorem 3.8 does NOT cover l = 5 (condition (b)
  excludes it via 2 * 3 * 5, condition (a) is far above it for a fixed
  curve), so it cannot by itself prove the uniform statement either.

* S1907FiniteVerification l0 -- an explicit mod-l Galois-image
  computation for the finitely many primes l < l0, in particular for
  l = 5, 7, 11, ....  No algorithm for this computation, and no
  formalized output of it, exists in the tree.

The file proves the logical decomposition

  S1907UniformTarget <-> exists l0, S1907Cofinite l0 and S1907Small l0

and the equivalence

  (exists l0, S1907Cofinite l0) <-> Set.Finite {l | not S1907Target l},

so that the first missing input is literally finiteness of the exceptional
set.  It introduces no axiom, no sorry, and no inhabitant of any missing
statement: S1907FirstMissing and S1907FiniteVerification are plain
Prop-valued definitions, exactly as the tree's other source gaps.

A note on the source quantifier: IUT I, Definition 3.1(c) fixes one prime l
as part of the initial Theta-data (l is a prime >= 5 whose mod-l image
contains SL_2(F_l)).  The paper therefore needs one admissible prime, not
the uniform statement over all l >= 5.  The uniform statement is stronger
than the source and is what S1894 isolated; this file records the stronger
statement as asked, and also proves that one witness already closes the
paper's D5 clause (S1907ExistsSourceTorsionClause_of_exists_target).

## Axiom footprint

All theorems below depend only on propext, Classical.choice and Quot.sound;
the checks are at the end of the file.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1907SerreLargeImageActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource.TorsionCarrierReduction
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1894D5LargeImageActual
open LeanFormal.IUT.Theorem311Source

/-! ## 1. The target and its S1894 forms -/

/-- The S1907 target at the prime l: the frozen Serre-style large-image
statement for the actual S1720 curve E' over F'. -/
def S1907Target (l : PrimeGeFive) : Prop :=
  SerreStyleLargeImageStatement S1720Curve l

/-- The target is literally S1894's exact missing input at l. -/
theorem S1907Target_iff_exactMissing (l : PrimeGeFive) :
    S1907Target l ↔ S1894ExactMissing l :=
  (S1894ExactMissing_iff_serre l).symm

/-- The target is literally the tree's existential-basis image statement. -/
theorem S1907Target_iff_imageContainsSL2 (l : PrimeGeFive) :
    S1907Target l ↔ S1725ImageContainsSL2 l :=
  (S1725ImageContainsSL2_iff_serre l).symm

/-- The uniform target: the large-image statement for every prime l >= 5.
This is the form S1894 isolated as the D5 remainder. -/
def S1907UniformTarget : Prop :=
  ∀ l : PrimeGeFive, S1907Target l

/-- The uniform target is the uniform exact-missing statement of S1894. -/
theorem S1907UniformTarget_iff_exactMissing :
    S1907UniformTarget ↔ ∀ l : PrimeGeFive, S1894ExactMissing l :=
  forall_congr' fun _ => S1907Target_iff_exactMissing _

/-- The uniform target is the uniform existential-basis form of S1725. -/
theorem S1907UniformTarget_iff_imageContainsSL2 :
    S1907UniformTarget ↔ ∀ l : PrimeGeFive, S1725ImageContainsSL2 l :=
  forall_congr' fun _ => S1907Target_iff_imageContainsSL2 _

/-- The target is enough for the paper's D5 clause.  At any prime l
satisfying the target, the S1894 D5 record for E'/F' exists; the rest of
Definition 3.1(c) is already a theorem for this curve (S1720/S1721/S1724/
S1725). -/
theorem S1907SourceTorsionClause_of_target (l : PrimeGeFive) (h : S1907Target l) :
    Nonempty (SourceTorsionClause.{0, 0, 0} l) :=
  S1894D5_of_serre l h

/-- The uniform target supplies the D5 record at every prime l >= 5. -/
theorem S1907SourceTorsionClause_of_uniform (h : S1907UniformTarget) :
    ∀ l : PrimeGeFive, Nonempty (SourceTorsionClause.{0, 0, 0} l) :=
  fun l => S1907SourceTorsionClause_of_target l (h l)

/-- A full GL_2(F_l) image in one basis is a sufficient certificate for the
target; this records a concrete shape a computation could produce. -/
theorem S1907Target_of_fullRange (l : PrimeGeFive) (b : S1725TorsionBasis l)
    (h : (S1720Curve.galoisLTorsionMatrixRepresentation l b).range = ⊤) :
    S1907Target l :=
  (S1907Target_iff_imageContainsSL2 l).mpr
    (S1894ImageContainsSL2_of_fullRange l b h)

/-! ## 2. Cofinite and finite parts of the uniform target -/

/-- The cofinite part: the target holds for every prime l with
l0 <= l.  Serre's open image theorem is a statement of this shape (with
an ineffective or explicit threshold l0). -/
def S1907Cofinite (l0 : ℕ) : Prop :=
  ∀ l : PrimeGeFive, l0 ≤ l.value → S1907Target l

/-- The finite part: the target holds at every prime below the threshold
l0.  This is a finite verification problem for the specific curve. -/
def S1907Small (l0 : ℕ) : Prop :=
  ∀ l : PrimeGeFive, l.value < l0 → S1907Target l

/-- Exact decomposition of the uniform target.  A proof of the uniform
statement is exactly a threshold l0, a proof of the cofinite statement
above l0, and a proof of the finite verification below l0. -/
theorem S1907UniformTarget_iff_split :
    S1907UniformTarget ↔ ∃ l0 : ℕ, S1907Cofinite l0 ∧ S1907Small l0 := by
  constructor
  · intro h
    exact ⟨0, fun l _ => h l, fun l _ => h l⟩
  · rintro ⟨l0, hc, hs⟩ l
    by_cases h : l.value < l0
    · exact hs l h
    · exact hc l (Nat.le_of_not_lt h)

/-- The cofinite statement and the finite verification at a common threshold
give the uniform target. -/
theorem S1907UniformTarget_of_cofinite_and_small {l0 : ℕ}
    (hc : S1907Cofinite l0) (hs : S1907Small l0) : S1907UniformTarget :=
  S1907UniformTarget_iff_split.mpr ⟨l0, hc, hs⟩

/-! ## 3. The exceptional set and the first missing input -/

/-- The exceptional set of the large-image statement: the primes at which
SL_2(F_l) is not contained in the image. -/
def S1907Exceptional : Set PrimeGeFive :=
  {l : PrimeGeFive | ¬ S1907Target l}

/-- The value map PrimeGeFive -> Nat is injective, so finiteness of the
exceptional set can be read off from finiteness of its set of values. -/
theorem S1907PrimeGeFive_value_injective :
    Function.Injective (fun l : PrimeGeFive => l.value) := by
  intro l l' h
  cases l with
  | mk v p g =>
  cases l' with
  | mk v' p' g' =>
  simp only at h
  subst h
  rfl

/-- The first missing input: only finitely many primes l >= 5 fail the
large-image statement.  This is the conclusion of Serre's open image theorem
(for the non-CM curve E'/F') and, in effective form, of [GenEll] Theorem
3.8; neither theorem is available in Lean.  This is a plain Prop; no
inhabitant is asserted. -/
def S1907FirstMissing : Prop :=
  ∃ l0 : ℕ, S1907Cofinite l0

/-- The second missing input at a threshold l0: the explicit finite mod-l
Galois-image verification for the primes below l0, in particular
l = 5, 7, 11, ....  This is the finite computation the cofinite theorems
do not supply. -/
def S1907FiniteVerification (l0 : ℕ) : Prop :=
  S1907Small l0

/-- Finiteness of the exceptional set is exactly the existence of a
threshold beyond which the target holds. -/
theorem S1907FirstMissing_iff_finite_exceptions :
    S1907FirstMissing ↔ S1907Exceptional.Finite := by
  constructor
  · rintro ⟨l0, h⟩
    have hsub : S1907Exceptional ⊆ {l : PrimeGeFive | l.value < l0} := by
      intro l hl
      by_contra hlt
      exact hl (h l (Nat.le_of_not_lt hlt))
    exact ((Set.finite_lt_nat l0).preimage
      (fun _ _ _ _ hab => S1907PrimeGeFive_value_injective hab)).subset hsub
  · intro hfin
    obtain ⟨M, hM⟩ := hfin.image (fun l : PrimeGeFive => l.value) |>.bddAbove
    refine ⟨M + 1, fun l hl => ?_⟩
    by_contra hnot
    have hmem : l ∈ S1907Exceptional := hnot
    have h1 : l.value ≤ M := hM (Set.mem_image_of_mem (fun l : PrimeGeFive => l.value) hmem)
    omega

/-- The exact remaining content of S1907.  The uniform target is
equivalent to: a threshold l0, the cofinite Serre/open-image input above
it, and the finite verification below it. -/
theorem S1907UniformTarget_iff_firstMissing_and_finite :
    S1907UniformTarget ↔
      ∃ l0 : ℕ, S1907Cofinite l0 ∧ S1907FiniteVerification l0 :=
  S1907UniformTarget_iff_split

/-- Recognition of the first missing input.  The uniform target supplies
the cofinite input and, for every threshold, the finite verification.  This
is the sense in which the uniform target is exactly open image + finite
check. -/
theorem S1907FirstMissing_and_finiteVerification_of_uniform
    (h : S1907UniformTarget) :
    S1907FirstMissing ∧ ∀ l0 : ℕ, S1907FiniteVerification l0 := by
  refine ⟨⟨0, fun l _ => h l⟩, fun l0 l _ => h l⟩

/-! ## 4. The paper's per-prime quantifier -/

/-- The prime 5, as an element of the l >= 5 label type. -/
def S1907Five : PrimeGeFive where
  value := 5
  prime := by norm_num
  ge_five := by norm_num

/-- A single witness of the target already gives a prime, so the uniform
target is stronger than the paper's Definition 3.1(c) needs. -/
theorem S1907ExistsTarget_of_uniform (h : S1907UniformTarget) :
    ∃ l : PrimeGeFive, S1907Target l :=
  ⟨S1907Five, h S1907Five⟩

/-- A single target witness already closes the paper's D5 clause for some
prime l >= 5.  This is the quantifier shape of IUT I, Definition 3.1(c),
where l is chosen as part of the initial Theta-data. -/
theorem S1907ExistsSourceTorsionClause_of_exists_target
    (h : ∃ l : PrimeGeFive, S1907Target l) :
    ∃ l : PrimeGeFive, Nonempty (SourceTorsionClause.{0, 0, 0} l) := by
  obtain ⟨l, hl⟩ := h
  exact ⟨l, S1907SourceTorsionClause_of_target l hl⟩

/-- Uniform form of the preceding statement. -/
theorem S1907ExistsSourceTorsionClause_of_uniform (h : S1907UniformTarget) :
    ∃ l : PrimeGeFive, Nonempty (SourceTorsionClause.{0, 0, 0} l) :=
  S1907ExistsSourceTorsionClause_of_exists_target (S1907ExistsTarget_of_uniform h)

/-! ## 5. What is already actual on the arithmetic side -/

/-- The arithmetic inputs of D5 for E'/F' that are already theorems in the
tree and are not part of the missing large-image input: split
multiplicative reduction at the selected bad place, l-coprimality there,
rationality of all six-torsion, and surjectivity of the representation onto
its range. -/
theorem S1907ArithmeticSide (l : PrimeGeFive) :
    S1720Curve.HasSplitMultiplicativeReductionAt (S1725D5Place l) ∧
      S1725LTorsionCompatible l ∧
      S1725SixTorsionIndependent ∧
      Function.Surjective (S1725Representation l) :=
  ⟨S1894SplitAtPlace l, S1894LTorsionCompatible_proved l,
    S1894SixTorsionIndependent, S1725Representation_surjective l⟩

/-! ## 6. Axiom footprint -/

#print axioms S1907Target_iff_exactMissing
#print axioms S1907Target_iff_imageContainsSL2
#print axioms S1907UniformTarget_iff_exactMissing
#print axioms S1907SourceTorsionClause_of_target
#print axioms S1907SourceTorsionClause_of_uniform
#print axioms S1907Target_of_fullRange
#print axioms S1907UniformTarget_iff_split
#print axioms S1907UniformTarget_of_cofinite_and_small
#print axioms S1907PrimeGeFive_value_injective
#print axioms S1907FirstMissing_iff_finite_exceptions
#print axioms S1907UniformTarget_iff_firstMissing_and_finite
#print axioms S1907FirstMissing_and_finiteVerification_of_uniform
#print axioms S1907ExistsTarget_of_uniform
#print axioms S1907ExistsSourceTorsionClause_of_exists_target
#print axioms S1907ExistsSourceTorsionClause_of_uniform
#print axioms S1907ArithmeticSide

end LeanFormal.IUT.XiFPaper.S1907SerreLargeImageActual
