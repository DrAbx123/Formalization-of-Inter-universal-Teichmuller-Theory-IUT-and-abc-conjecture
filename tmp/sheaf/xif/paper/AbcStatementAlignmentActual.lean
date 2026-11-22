import LeanFormal.IUT.ABCBridge.Statement
import tmp.external.ported.tauceti_belyi_core.TauCeti.NumberTheory.AbcConjecture

/-! # AbcStatementAlignment: LeanFormal.IUT.ABCConjecture ↔ TauCeti.AbcConjecture

This file bridges our ABC statement (`LeanFormal.IUT.ABCBridge.Statement`,
over `LeanFormal.IUT.radical := UniqueFactorizationMonoid.radical` and
`IsABCTriple = PrimitiveAdditiveTriple`) to Tau Ceti's standard statement
(`TauCeti.AbcConjecture`, from the ported `tauceti_belyi_core` closure).

STEP 0 prior art: our `radical` is definitionally `UniqueFactorizationMonoid.radical`
(Foundations/Arithmetic/Radical.lean:17); the ported Tau Ceti file opens
`UniqueFactorizationMonoid` (line 74), so the radical bridge is rfl. Tau Ceti's
`abcConjectureWithExponent_iff_nat` provides the positive-coprime-natural form.
Registry frozen 14041; no registry edits; no gate changes. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.AbcStatementAlignmentActual

open LeanFormal.IUT

/-- Our `radical` is Tau Ceti's radical (both `UniqueFactorizationMonoid.radical`). -/
theorem radical_eq_ufm (n : Nat) : radical n = UniqueFactorizationMonoid.radical n := rfl

/-- Tau Ceti abc conjecture, unfolded to the positive-coprime-natural form. -/
theorem tauCeti_nat_form :
    TauCeti.AbcConjecture ↔
      ∀ ε : Real, 0 < ε → ∃ C : Real, ∀ a b c : Nat,
        0 < a → 0 < b → a.Coprime b → a + b = c →
          (c : Real) ≤ C * ((UniqueFactorizationMonoid.radical (a * b * c) : Nat) : Real) ^ (1 + ε) :=
  TauCeti.abcConjectureWithExponent_iff_nat 1 (by norm_num)

/-- **Main alignment:** our integer ABC conjecture is equivalent to Tau Ceti's. -/
theorem abcConjecture_iff_tauCeti :
    LeanFormal.IUT.ABCConjecture ↔ TauCeti.AbcConjecture := by
  constructor
  · intro hI
    rw [tauCeti_nat_form]
    intro ε hε
    obtain ⟨K, hKpos, hK⟩ := hI ε hε
    refine ⟨K, fun a b c ha hb hab hsum => ?_⟩
    have h := hK a b c ⟨ha, hb, hsum, hab⟩
    exact h
  · intro hTau
    rw [tauCeti_nat_form] at hTau
    intro ε hε
    obtain ⟨C, hC⟩ := hTau ε hε
    refine ⟨max C 0 + 1, ?_, fun a b c htri => ?_⟩
    · nlinarith [le_max_right C 0]
    · obtain ⟨ha, hb, hsum, hab⟩ := htri
      have h := hC a b c ha hb hab hsum
      have hR : (0 : Real) ≤
          ((UniqueFactorizationMonoid.radical (a * b * c) : Nat) : Real) ^ (1 + ε) :=
        Real.rpow_nonneg (by positivity) _
      have hle : C ≤ max C 0 + 1 := by nlinarith [le_max_left C 0]
      have hmul :
          C * ((UniqueFactorizationMonoid.radical (a * b * c) : Nat) : Real) ^ (1 + ε) ≤
            (max C 0 + 1) *
              ((UniqueFactorizationMonoid.radical (a * b * c) : Nat) : Real) ^ (1 + ε) :=
        mul_le_mul_of_nonneg_right hle hR
      exact le_trans h hmul

theorem alignment_directions :
    (LeanFormal.IUT.ABCConjecture → TauCeti.AbcConjecture) ∧
      (TauCeti.AbcConjecture → LeanFormal.IUT.ABCConjecture) :=
  ⟨abcConjecture_iff_tauCeti.mp, abcConjecture_iff_tauCeti.mpr⟩

#check abcConjecture_iff_tauCeti
#check tauCeti_nat_form

end LeanFormal.IUT.XiFPaper.AbcStatementAlignmentActual
end