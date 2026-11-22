/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import tmp.sheaf.xif.paper.S1992RebasedLocalInputActual
import Mathlib.FieldTheory.Extension
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Ext
import Mathlib.Tactic.Group

/-!
# S1996: actual local decorations for the S1992 rebased family

Layer: **O** (original Theta-link / q-pilot), direct worker of S1992.

## The gap

S1992 reduces S1978's rebased input exactly to `S1992RebasedLocalFamily D`.
That datum must supply infinitely many pairwise distinct F-prime-strips, each
linked to the actual local `O^×` strip `localOFieldStrip`.  The remaining
freedom at a place is the decoration triple
`(Pi_v ≃ Pi_v, G_v ≃ G_v, O^×_v ≃ O^×_v)`, and the decoration data must be
provably pairwise distinct on `(proj, action)`.

## What is proved here

1. **An actual non-identity local Galois automorphism.**  In the algebraic
   closure of `Q_5` we construct a square root `sqrt5` of `5` and a genuine
   `Q_5`-algebra automorphism `swapSqrt5` of the full local algebraic closure
   with `swapSqrt5 sqrt5 = -sqrt5`.  It is proved non-identity.  The proof
   uses the irreducibility of `X^2 - 5` over `Q_5`, which follows from
   valuation parity (`5` is not a square in `Q_5`).

2. **Actual non-Galois-invariant local units.**  For every integer `a` we
   construct the actual unit `1 + a * sqrt5` of the valuation ring, with
   explicit inverse `(1 - a * sqrt5) / (1 - 5*a^2)`.  These units are
   pairwise distinct.

3. **The proposed `u ↦ c * u` is not a `MulAut`.**  For any group `G` and
   `c : G`, a multiplicative automorphism whose underlying function is
   `u ↦ c * u` exists only when `c = 1`: evaluating at `1` gives `c = 1`.
   Consequently the suggested conjugation by `alpha_c : u ↦ c * u` cannot
   produce a non-identity decoration of the local `O^×` carrier.  This is a
   real obstruction, not a missing proof: the map is a permutation of the
   underlying set but is not a group homomorphism when `c != 1`.
   The actual Galois-induced automorphism `swapSqrt5UnitAut` is a genuine
   non-identity `MulAut`, and is proved not to be left translation by any
   unit; but proving that its conjugate of the local action is non-identity
   (or producing an infinite family with pairwise distinct conjugates) is the
   remaining input.

4. **The exact remaining missing datum.**  A genuine decoration of the unit
   component requires a family of actual group automorphisms
   `alpha_i : MulAut (LocalOFieldUnits 5)` whose conjugates of the actual
   local Galois action are pairwise distinct.  This is recorded as
   `S1996UnitDecorationFamily`.  The corresponding strip-level missing datum
   is `S1996LocalFPrimeStripFamily`: an infinite family of pairwise distinct
   F-prime-strips linked to `localOFieldStrip`.  We prove that every
   `S1992RebasedLocalFamily` yields such a strip family, so the recorded
   structure is a necessary part of S1992's exact missing datum.

## What is *not* faked

No `sorry`, `axiom`, `True`/`PUnit` slot, empty type, arbitrary inhabitant or
`Nonempty` gate is used.  The missing family is a structure with no asserted
inhabitant.  The negative theorem about `u ↦ c * u` is proved, not assumed.

The construction of an infinite family of actual `MulAut`s of
`LocalOFieldUnits 5` whose conjugates of the local Galois action are pairwise
distinct (or of a non-inner automorphism of the local absolute Galois group) is
the precise remaining mathematical input.  A single nontrivial `MulAut`
(`swapSqrt5UnitAut`) is constructed, but its conjugate action is not proved to
differ from the original action.  Merely having a non-Galois-invariant
*element* `c` of `O^×` is not enough, because left multiplication by `c` is not
a group automorphism.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1996LocalDecorationsActual

open Polynomial
open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.S1978LocalFieldOCarrierActual
open LeanFormal.IUT.XiFPaper.S1992RebasedLocalInputActual

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-! ## 1. The local algebraic closure and sqrt 5 -/

abbrev K5 : Type := AlgebraicClosure ℚ_[5]

abbrev PV : Type := LeanFormal.IUT.XiFPaper.S1951KummerEvaluationSquareActual.PaperV

/-- `5` is not a square in `Q_5`: valuation parity. -/
theorem five_not_square (b : ℚ_[5]) : b ^ 2 ≠ 5 := by
  intro hb
  have hv := congrArg Padic.valuation hb
  rw [Padic.valuation_pow] at hv
  rw [Padic.valuation_ofNat] at hv
  rw [padicValNat_self] at hv
  norm_num at hv
  omega

theorem five_irreducible : Irreducible ((X : ℚ_[5][X]) ^ 2 - Polynomial.C 5) :=
  X_pow_sub_C_irreducible_of_prime (p := 2) Nat.prime_two five_not_square

/-- A chosen square root of `5` in the algebraic closure of `Q_5`. -/
noncomputable def sqrt5 : K5 :=
  Classical.choose (IsAlgClosed.exists_eq_mul_self (5 : K5))

theorem sqrt5_sq : sqrt5 ^ 2 = 5 := by
  have h := (Classical.choose_spec (IsAlgClosed.exists_eq_mul_self (5 : K5))).symm
  simpa [sqrt5, pow_two] using h

theorem sqrt5_mul_self : sqrt5 * sqrt5 = (5 : K5) := by
  rw [← pow_two, sqrt5_sq]

theorem sqrt5_ne_zero : sqrt5 ≠ 0 := by
  intro h
  have h5 : (5 : K5) = 0 := by rw [← sqrt5_sq, h]; norm_num
  exact (by norm_num : (5 : K5) ≠ 0) h5

theorem sqrt5_root :
    Polynomial.aeval sqrt5 ((X : ℚ_[5][X]) ^ 2 - Polynomial.C 5) = 0 := by
  rw [map_sub, map_pow, aeval_X, aeval_C, sqrt5_sq]
  rw [map_ofNat]
  ring

theorem minpoly_sqrt5 :
    minpoly ℚ_[5] sqrt5 = (X : ℚ_[5][X]) ^ 2 - Polynomial.C 5 :=
  (minpoly.eq_of_irreducible_of_monic five_irreducible sqrt5_root
    (monic_X_pow_sub_C 5 (by norm_num))).symm

theorem aeval_neg_sqrt5_minpoly :
    Polynomial.aeval (-sqrt5) (minpoly ℚ_[5] sqrt5) = 0 := by
  rw [minpoly_sqrt5, map_sub, map_pow, aeval_X, aeval_C]
  have h : (-sqrt5) ^ 2 = (5 : K5) := by rw [neg_sq, sqrt5_sq]
  rw [h, map_ofNat]
  ring

/-- The non-identity automorphism of the local absolute Galois group at `5`
sending `sqrt5` to `-sqrt5`. -/
noncomputable def swapSqrt5Hom : K5 →ₐ[ℚ_[5]] K5 :=
  Classical.choose (IntermediateField.exists_algHom_of_splits_of_aeval
    (F := ℚ_[5]) (E := K5) (K := K5)
    (fun s => ⟨(Algebra.IsAlgebraic.isAlgebraic s).isIntegral, IsAlgClosed.splits _⟩)
    (x := sqrt5) (y := -sqrt5) aeval_neg_sqrt5_minpoly)

theorem swapSqrt5Hom_apply : swapSqrt5Hom sqrt5 = -sqrt5 :=
  Classical.choose_spec (IntermediateField.exists_algHom_of_splits_of_aeval
    (F := ℚ_[5]) (E := K5) (K := K5)
    (fun s => ⟨(Algebra.IsAlgebraic.isAlgebraic s).isIntegral, IsAlgClosed.splits _⟩)
    (x := sqrt5) (y := -sqrt5) aeval_neg_sqrt5_minpoly)

noncomputable def swapSqrt5 : LocalAbsoluteGalois 5 :=
  AlgEquiv.ofBijective swapSqrt5Hom (Algebra.IsAlgebraic.algHom_bijective swapSqrt5Hom)

theorem swapSqrt5_apply : swapSqrt5 sqrt5 = -sqrt5 := swapSqrt5Hom_apply

theorem swapSqrt5_ne_one : swapSqrt5 ≠ 1 := by
  intro h
  have h' : -sqrt5 = sqrt5 := by
    have := congrArg (fun f : LocalAbsoluteGalois 5 => f sqrt5) h
    simpa [swapSqrt5_apply] using this
  have hs : sqrt5 = -sqrt5 := neg_eq_iff_eq_neg.mp h'
  have h2 : (2 : K5) * sqrt5 = 0 := by
    have hh : sqrt5 + sqrt5 = 0 := by
      calc sqrt5 + sqrt5 = (-sqrt5) + sqrt5 := congrArg (fun x => x + sqrt5) hs
        _ = 0 := by ring
    simpa [two_mul] using hh
  have hzero : sqrt5 = 0 := (mul_eq_zero.mp h2).resolve_left (by norm_num)
  exact sqrt5_ne_zero hzero

/-! ## 2. The actual units `1 + a * sqrt 5` -/

def r (a : ℤ) : ℚ_[5] := 1 - 5 * (a : ℚ_[5]) ^ 2

theorem norm5 : ‖(5 : K5)‖ = (5 : ℝ)⁻¹ := by
  rw [show (5 : K5) = algebraMap ℚ_[5] K5 5 by rw [map_ofNat]]
  rw [norm_algebraMap']
  change ‖((5 : ℕ) : ℚ_[5])‖ = (5 : ℝ)⁻¹
  rw [Padic.norm_p]
  norm_num

theorem norm_sqrt5_sq : ‖sqrt5‖ ^ 2 = (5 : ℝ)⁻¹ := by
  rw [← norm_pow, sqrt5_sq, norm5]

theorem norm_sqrt5_le_one : ‖sqrt5‖ ≤ 1 := by
  have h : ‖sqrt5‖ ^ 2 = (5 : ℝ)⁻¹ := norm_sqrt5_sq
  nlinarith [norm_nonneg sqrt5]

theorem norm_a_mul_sqrt5_le_one (a : ℤ) : ‖(a : K5) * sqrt5‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one K5 a)
    (norm_nonneg _) norm_sqrt5_le_one

theorem norm_one_add_a_mul_sqrt5 (a : ℤ) :
    ‖(1 : K5) + (a : K5) * sqrt5‖ ≤ 1 := by
  have h := IsUltrametricDist.norm_add_le_max (1 : K5) ((a : K5) * sqrt5)
  exact h.trans (max_le (by norm_num) (norm_a_mul_sqrt5_le_one a))

theorem norm_one_sub_a_mul_sqrt5 (a : ℤ) :
    ‖(1 : K5) - (a : K5) * sqrt5‖ ≤ 1 := by
  have h := IsUltrametricDist.norm_add_le_max (1 : K5) (-((a : K5) * sqrt5))
  have hneg : ‖-((a : K5) * sqrt5)‖ ≤ 1 := by
    rw [norm_neg]
    exact norm_a_mul_sqrt5_le_one a
  simpa [sub_eq_add_neg] using h.trans (max_le (by norm_num) hneg)

theorem norm_r (a : ℤ) : ‖r a‖ = 1 := by
  have hcop : IsCoprime (1 - 5 * a ^ 2) (5 : ℤ) := ⟨1, a ^ 2, by ring⟩
  rw [show r a = ((1 - 5 * a ^ 2 : ℤ) : ℚ_[5]) by
    unfold r; push_cast; ring]
  exact Padic.norm_intCast_eq_one_iff.mpr hcop

theorem r_ne_zero (a : ℤ) : r a ≠ 0 := by
  intro h
  have := norm_r a
  rw [h, norm_zero] at this
  norm_num at this

theorem norm_inv_factor (a : ℤ) :
    ‖algebraMap ℚ_[5] K5 (r a)⁻¹‖ ≤ 1 := by
  rw [norm_algebraMap', norm_inv, norm_r]
  norm_num

theorem norm_decorationInv (a : ℤ) :
    ‖(algebraMap ℚ_[5] K5 (r a)⁻¹) * ((1 : K5) - (a : K5) * sqrt5)‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ (norm_inv_factor a) (norm_nonneg _) (norm_one_sub_a_mul_sqrt5 a)

theorem prod_eq_r (a : ℤ) :
    (1 + (a : K5) * sqrt5) * (1 - (a : K5) * sqrt5) =
      algebraMap ℚ_[5] K5 (r a) := by
  have hcast : algebraMap ℚ_[5] K5 (r a) = 1 - (5 : K5) * (a : K5) ^ 2 := by
    unfold r
    rw [map_sub, map_mul, map_pow, map_one, map_intCast, map_ofNat]
  rw [hcast]
  ring_nf
  rw [sqrt5_sq]

/-- The actual unit `1 + a * sqrt5` of the local valuation ring. -/
noncomputable def decorationUnit (a : ℤ) : LocalOFieldUnits 5 where
  val := ⟨1 + (a : K5) * sqrt5,
    (mem_integers_iff _).mpr (norm_one_add_a_mul_sqrt5 a)⟩
  inv := ⟨(algebraMap ℚ_[5] K5 (r a)⁻¹) * (1 - (a : K5) * sqrt5),
    (mem_integers_iff _).mpr (norm_decorationInv a)⟩
  val_inv := by
    apply Subtype.ext
    change (1 + (a : K5) * sqrt5) *
      ((algebraMap ℚ_[5] K5 (r a)⁻¹) * (1 - (a : K5) * sqrt5)) = 1
    calc (1 + (a : K5) * sqrt5) *
          ((algebraMap ℚ_[5] K5 (r a)⁻¹) * (1 - (a : K5) * sqrt5))
        = (algebraMap ℚ_[5] K5 (r a)⁻¹) *
            ((1 + (a : K5) * sqrt5) * (1 - (a : K5) * sqrt5)) := by ring
      _ = (algebraMap ℚ_[5] K5 (r a)⁻¹) * algebraMap ℚ_[5] K5 (r a) := by
        rw [prod_eq_r]
      _ = 1 := by rw [← map_mul, inv_mul_cancel₀ (r_ne_zero a), map_one]
  inv_val := by
    apply Subtype.ext
    change ((algebraMap ℚ_[5] K5 (r a)⁻¹) * (1 - (a : K5) * sqrt5)) *
      (1 + (a : K5) * sqrt5) = 1
    calc ((algebraMap ℚ_[5] K5 (r a)⁻¹) * (1 - (a : K5) * sqrt5)) *
          (1 + (a : K5) * sqrt5)
        = (algebraMap ℚ_[5] K5 (r a)⁻¹) *
            ((1 + (a : K5) * sqrt5) * (1 - (a : K5) * sqrt5)) := by ring
      _ = (algebraMap ℚ_[5] K5 (r a)⁻¹) * algebraMap ℚ_[5] K5 (r a) := by
        rw [prod_eq_r]
      _ = 1 := by rw [← map_mul, inv_mul_cancel₀ (r_ne_zero a), map_one]

@[simp] theorem decorationUnit_val (a : ℤ) :
    ((decorationUnit a : LocalOFieldUnits 5) : K5) = 1 + (a : K5) * sqrt5 := rfl

theorem decorationUnit_injective : Function.Injective decorationUnit := by
  intro a b h
  have hval : (1 : K5) + (a : K5) * sqrt5 = 1 + (b : K5) * sqrt5 := by
    simpa using congrArg (fun u : LocalOFieldUnits 5 => (u : K5)) h
  have hmul : (a : K5) * sqrt5 = (b : K5) * sqrt5 := by
    simpa using congrArg (fun z : K5 => z - 1) hval
  have hzero : ((a : K5) - (b : K5)) * sqrt5 = 0 := by
    rw [sub_mul, hmul, sub_self]
  have hsub : (a : K5) - (b : K5) = 0 := (mul_eq_zero.mp hzero).resolve_right sqrt5_ne_zero
  have hab : (a : K5) = (b : K5) := sub_eq_zero.mp hsub
  exact_mod_cast hab

theorem decorationUnit_zero : decorationUnit 0 = 1 := by
  apply Units.ext
  apply Subtype.ext
  simp [decorationUnit]

/-- The actual multiplicative automorphism of the local `O^×` carrier induced by
`swapSqrt5`.  This is genuine nontrivial `MulAut` data (unlike left translation
by a unit). -/
noncomputable def swapSqrt5UnitAut : MulAut (LocalOFieldUnits 5) :=
  localOFieldUnitsMulAut 5 swapSqrt5

theorem localGaloisUnitMap_val (σ : LocalAbsoluteGalois 5)
    (u : LocalOFieldUnits 5) :
    ((localGaloisUnitMap σ u : LocalOFieldUnits 5) : K5) = σ (u : K5) := rfl

theorem swapSqrt5UnitAut_apply_decorationUnit (a : ℤ) :
    swapSqrt5UnitAut (decorationUnit a) = decorationUnit (-a) := by
  apply Units.ext
  apply Subtype.ext
  change ((localGaloisUnitMap swapSqrt5 (decorationUnit a) : LocalOFieldUnits 5) : K5) =
    ((decorationUnit (-a) : LocalOFieldUnits 5) : K5)
  rw [localGaloisUnitMap_val, decorationUnit_val, decorationUnit_val]
  simp [map_add, map_mul, map_one, swapSqrt5_apply]

theorem swapSqrt5UnitAut_ne_one : swapSqrt5UnitAut ≠ 1 := by
  intro h
  have h' := congrArg (fun f : MulAut (LocalOFieldUnits 5) => f (decorationUnit 1)) h
  rw [swapSqrt5UnitAut_apply_decorationUnit] at h'
  have h2 : (-1 : ℤ) = 1 := decorationUnit_injective h'
  norm_num at h2

/-- The actual Galois-induced unit automorphism is not left translation by
any unit.  In particular it is genuinely beyond the proposed `u ↦ c * u`
construction. -/
theorem swapSqrt5UnitAut_not_leftTranslation :
    ¬ ∃ c : LocalOFieldUnits 5, ∀ u, swapSqrt5UnitAut u = c * u := by
  rintro ⟨c, hc⟩
  have hc1 : c = 1 := by simpa [eq_comm] using hc 1
  apply swapSqrt5UnitAut_ne_one
  ext u
  rw [hc u, hc1, one_mul]
  rfl

/-! ## 3. The proposed left multiplication is not a multiplicative automorphism -/

/-- If a multiplicative automorphism of a group has underlying function
`u ↦ c * u`, then `c = 1`.  Evaluating at `1` gives `c = 1`. -/
theorem mulAut_mulLeft_eq_one {G : Type*} [Group G] (c : G) (f : MulAut G)
    (hf : ∀ u, f u = c * u) : c = 1 := by
  have h := hf 1
  simpa [eq_comm] using h

/-- For `c ≠ 1`, no multiplicative automorphism of `G` is left translation
by `c`.  In particular the suggested `alpha_c : u ↦ c * u` is not an
automorphism of the local `O^×` carrier. -/
theorem no_mulAut_mulLeft {G : Type*} [Group G] (c : G) (hc : c ≠ 1) :
    ¬ ∃ f : MulAut G, ∀ u, f u = c * u := by
  rintro ⟨f, hf⟩
  exact hc (mulAut_mulLeft_eq_one c f hf)

theorem decorationUnit_ne_one (a : ℤ) (ha : a ≠ 0) : decorationUnit a ≠ 1 := by
  intro h
  apply ha
  have h' : decorationUnit a = decorationUnit 0 := by
    rw [h]
    apply Units.ext
    apply Subtype.ext
    simp [decorationUnit]
  exact decorationUnit_injective h'

/-! ## 4. The exact missing decoration datum -/

/-- The genuine unit-automorphism decoration datum: an infinite family of
actual `MulAut`'s of the local `O^×` whose conjugates of the local Galois
action are pairwise distinct.  This is the precise missing input for the
unit-component route to S1992's decoration family. -/
structure S1996UnitDecorationFamily where
  index : Type
  infinite_index : Infinite index
  aut : index → MulAut (LocalOFieldUnits 5)
  conj_injective : Function.Injective (fun i =>
    (MulAut.conj (aut i)).toMonoidHom.comp (LocalOFieldUnitsAction 5))

namespace S1996UnitDecorationFamily

variable (F : S1996UnitDecorationFamily)

theorem aut_ne_one {i j : F.index} (hij : i ≠ j) : F.aut i ≠ F.aut j := by
  intro h
  apply hij
  apply F.conj_injective
  simp only [h]

end S1996UnitDecorationFamily

/-- **The exact missing at the strip level.**  An infinite family of pairwise
distinct F-prime-strips, each linked to the actual local `O^×` strip, with
the `(1,0)` member equal to `localOFieldStrip`.  This is exactly the
prime-strip part of S1992's missing family. -/
structure S1996LocalFPrimeStripFamily where
  index : Type
  index_equiv : index ≃ LeanFormal.IUT.Theorem311Source.SourceTheorem311Index
  strip : index → FPrimeStrip PV
  strip_injective : Function.Injective strip
  linked : ∀ i, Nonempty (FPrimeStripEquiv localOFieldStrip (strip i))
  core_index : index
  core_eq : strip core_index = localOFieldStrip

namespace S1996LocalFPrimeStripFamily

variable (F : S1996LocalFPrimeStripFamily)

/-- The index of a strip family is infinite, because it is equivalent to
S1992's `Int × Int` index. -/
noncomputable instance infiniteIndex : Infinite F.index :=
  Infinite.of_injective F.index_equiv.symm F.index_equiv.symm.injective

end S1996LocalFPrimeStripFamily

namespace S1992RebasedLocalFamily

variable {D : LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual.S1895PaperInput}
  (E : S1992RebasedLocalFamily D)

/-- Every inhabitant of S1992's exact missing datum yields the strip-level
decoration family recorded as `S1996LocalFPrimeStripFamily`. -/
noncomputable def toLocalFPrimeStripFamily : S1996LocalFPrimeStripFamily where
  index := E.family.index
  index_equiv := E.index_equiv
  strip := fun i => (E.family.theater i).primeStrip
  strip_injective := E.strip_injective
  linked := E.other_strip_linked
  core_index := E.index_equiv.symm (1, 0)
  core_eq := E.core_eq_local

end S1992RebasedLocalFamily

/-- The exact first missing of this file: the strip-level decoration family
needed by S1992.  No inhabitant is constructed. -/
abbrev S1996FirstMissing := S1996LocalFPrimeStripFamily

/-- The suggested `u ↦ c * u` route cannot provide a non-identity unit
decoration, because such a map is not a `MulAut` unless `c = 1`.  This is the
precise obstruction to the literal construction proposed for S1996. -/
theorem suggested_left_multiplication_obstruction (c : LocalOFieldUnits 5)
    (hc : c ≠ 1) :
    ¬ ∃ f : MulAut (LocalOFieldUnits 5), ∀ u, f u = c * u :=
  no_mulAut_mulLeft c hc

/-! ## 5. Axiom probes -/

#print axioms five_not_square
#print axioms swapSqrt5
#print axioms swapSqrt5_ne_one
#print axioms decorationUnit
#print axioms decorationUnit_injective
#print axioms swapSqrt5UnitAut
#print axioms swapSqrt5UnitAut_ne_one
#print axioms swapSqrt5UnitAut_apply_decorationUnit
#print axioms swapSqrt5UnitAut_not_leftTranslation
#print axioms no_mulAut_mulLeft
#print axioms S1996UnitDecorationFamily.aut_ne_one
#print axioms S1996LocalFPrimeStripFamily.infiniteIndex
#print axioms S1992RebasedLocalFamily.toLocalFPrimeStripFamily

end LeanFormal.IUT.XiFPaper.S1996LocalDecorationsActual
