/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.Arithmetic.Radical
import LeanFormal.IUT.Foundations.Arithmetic.PrimitiveAdditive
import LeanFormal.IUT.ABCBridge.Statement
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# A743 ABC dictionary (mainline): LANA classical ABC <-> our ABC statement

* `natRadical_eq_ufmRadical` : our `natRadical` IS the UFM radical (rfl);
* `isABCTriple_iff_lana` : `IsABCTriple` = primitive additive triple, in LANA order;
* `rpow_eq_hpow` : on `R` the two spellings of a real power coincide;
* `abcConstant_pos` : raise the ABC constant to a positive one;
* `abcBound_constant_pos` : constant form implies the standard `ABCConjecture`.

No axiom/sorry; ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1AbcDictionaryActual

open LeanFormal.IUT

/-- Our `natRadical` is Mathlib's `UniqueFactorizationMonoid.radical`. -/
theorem natRadical_eq_ufmRadical (n : Nat) :
    LeanFormal.IUT.natRadical n = UniqueFactorizationMonoid.radical n := rfl

/-- `IsABCTriple` in the LANA order of conjuncts. -/
theorem isABCTriple_iff_lana (a b c : Nat) :
    IsABCTriple a b c ↔ (0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧ a + b = c) := by
  unfold IsABCTriple PrimitiveAdditiveTriple
  constructor
  · rintro ⟨ha, hb, hsum, hcop⟩
    exact ⟨ha, hb, hcop, hsum⟩
  · rintro ⟨ha, hb, hcop, hsum⟩
    exact ⟨ha, hb, hsum, hcop⟩

/-- On `Real`, `Real.rpow` and the `^` power notation agree by definition. -/
theorem rpow_eq_hpow (x y : Real) : Real.rpow x y = x ^ y := rfl

/-- Raise a constant in a monotone predicate to a positive one. -/
theorem abcConstant_pos {P : Real → Real → Prop}
    (h : ∀ ε > 0, ∃ C, P ε C)
    (hmono : ∀ ε C K, C ≤ K → P ε C → P ε K) :
    ∀ ε > 0, ∃ K > 0, P ε K := by
  intro ε hε
  obtain ⟨C, hC⟩ := h ε hε
  exact ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right C 1),
    hmono ε C (max C 1) (le_max_left C 1) hC⟩

/-- The epsilon-constant radical bound in our normalized form implies `ABCConjecture`. -/
theorem abcBound_constant_pos
    (h : ∀ ε > 0, ∃ C : Real, ∀ a b c : Nat, IsABCTriple a b c →
      (c : Real) ≤ C * Real.rpow (LeanFormal.IUT.radical (a * b * c) : Real) (1 + ε)) :
    LeanFormal.IUT.ABCConjecture := by
  intro ε hε
  obtain ⟨C, hC⟩ := h ε hε
  refine ⟨max C 1, ?_, ?_⟩
  · exact lt_of_lt_of_le one_pos (le_max_right C 1)
  · intro a b c habc
    have hbase : (0 : Real) ≤ Real.rpow (LeanFormal.IUT.radical (a * b * c) : Real) (1 + ε) :=
      Real.rpow_nonneg (by exact_mod_cast Nat.zero_le _) _
    calc
      (c : Real) ≤ C * Real.rpow (LeanFormal.IUT.radical (a * b * c) : Real) (1 + ε) :=
        hC a b c habc
      _ ≤ max C 1 * Real.rpow (LeanFormal.IUT.radical (a * b * c) : Real) (1 + ε) :=
        mul_le_mul_of_nonneg_right (le_max_left C 1) hbase

end LeanFormal.IUT.XiFPaper.Mzk1AbcDictionaryActual

end

/-! ### Axiom gates (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1AbcDictionaryActual.natRadical_eq_ufmRadical
#print axioms LeanFormal.IUT.XiFPaper.Mzk1AbcDictionaryActual.isABCTriple_iff_lana
#print axioms LeanFormal.IUT.XiFPaper.Mzk1AbcDictionaryActual.abcBound_constant_pos