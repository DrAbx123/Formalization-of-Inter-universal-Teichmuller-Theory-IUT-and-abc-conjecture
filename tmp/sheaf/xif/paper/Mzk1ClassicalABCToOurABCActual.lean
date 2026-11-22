import LeanFormal.IUT.ABCBridge.Statement
import tmp.sheaf.xif.paper.Mzk1AbcDictionaryActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# stepxi ClassicalABC-shape -> our ABCConjecture (olean-independent check)

The proof of `abcConjecture_of_classicalABC` in
`Mzk1SSIneqConsumerChainActual` is checked here against a local definition with
exactly the lana `Iut.ClassicalABC` shape (same quantifiers/order/radical/rpow). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ClassicalABCToOurABCActual

open LeanFormal.IUT

/-- Local copy of lana `Iut.ClassicalABC` shape. -/
def ClassicalABCShape : Prop :=
  ∀ ε : Real, 0 < ε → ∃ C : Real,
    ∀ a b c : Nat, 0 < a → 0 < b → Nat.Coprime a b → a + b = c →
      (c : Real) ≤ C * ((UniqueFactorizationMonoid.radical (a * b * c) : Nat) : Real) ^ (1 + ε)

theorem abcConjecture_of_classicalABCShape (h : ClassicalABCShape) :
    ABCConjecture := by
  intro ε hε
  obtain ⟨C, hC⟩ := h ε hε
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right C 1), ?_⟩
  intro a b c habc
  obtain ⟨ha, hb, hcop, hsum⟩ :=
    (Mzk1AbcDictionaryActual.isABCTriple_iff_lana a b c).mp habc
  have hineq := hC a b c ha hb hcop hsum
  have hineq' : (c : Real) ≤ C * Real.rpow
      ((LeanFormal.IUT.radical (a * b * c) : Nat) : Real) (1 + ε) := by
    simpa [Mzk1AbcDictionaryActual.natRadical_eq_ufmRadical,
      LeanFormal.IUT.radical, Mzk1AbcDictionaryActual.rpow_eq_hpow] using hineq
  unfold ABCInequality
  have hpow_nonneg : (0 : Real) ≤ Real.rpow
      ((LeanFormal.IUT.radical (a * b * c) : Nat) : Real) (1 + ε) :=
    Real.rpow_nonneg (by exact_mod_cast Nat.zero_le _) _
  calc (c : Real) ≤ C * Real.rpow
        ((LeanFormal.IUT.radical (a * b * c) : Nat) : Real) (1 + ε) := hineq'
    _ ≤ max C 1 * Real.rpow
        ((LeanFormal.IUT.radical (a * b * c) : Nat) : Real) (1 + ε) :=
        mul_le_mul_of_nonneg_right (le_max_left C 1) hpow_nonneg

end LeanFormal.IUT.XiFPaper.Mzk1ClassicalABCToOurABCActual

end
