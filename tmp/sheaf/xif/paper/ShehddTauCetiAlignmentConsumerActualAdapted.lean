import tmp.sheaf.xif.paper.AbcStatementAlignmentActual
import LeanFormal.IUT.ABCBridge.Arithmetic.LogarithmicBoundEquivalence

/-!
# ShehddTauCetiAlignmentConsumerActualAdapted — Tau Ceti / log-form ABC alignment consumer

STEP 0 prior-art (reuse only; A475 search: statement alignment asset found):
* AbcStatementAlignmentActual: radical_eq_ufm, tauCeti_nat_form,
  abcConjecture_iff_tauCeti, alignment_directions;
* LogarithmicBoundEquivalence: radical_eq_natRadical, ABCLogConjecture,
  abcConjecture_iff_abcLogConjecture (via IUTToABC).

This file composes the statement alignment with the log-form equivalence: Tau Ceti's ABC
is equivalent to the log form, and the two radical aliases are identified.  No new
assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddTauCetiAlignmentConsumerActualAdapted

open LeanFormal.IUT

/-- **PROVED consumer:** Tau Ceti's ABC is equivalent to our log form. -/
theorem tauCeti_iff_abcLogConjecture :
    TauCeti.AbcConjecture ↔ ABCLogConjecture :=
  AbcStatementAlignmentActual.abcConjecture_iff_tauCeti.symm.trans
    abcConjecture_iff_abcLogConjecture

/-- **PROVED consumer:** the two radical aliases (statement radical, UFM radical) are
the same constant as the sibling `natRadical`. -/
theorem radical_aliases_consumer (n : Nat) :
    radical n = natRadical n ∧
      radical n = UniqueFactorizationMonoid.radical n :=
  ⟨radical_eq_natRadical n, AbcStatementAlignmentActual.radical_eq_ufm n⟩

/-- **PROVED consumer:** Tau Ceti's nat form, restated as a consumer interface. -/
theorem tauCeti_nat_form_consumer :
    TauCeti.AbcConjecture ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ a b c : Nat,
        0 < a → 0 < b → a.Coprime b → a + b = c →
          (c : ℝ) ≤ C * ((UniqueFactorizationMonoid.radical (a * b * c) : Nat) : ℝ) ^ (1 + ε) :=
  AbcStatementAlignmentActual.tauCeti_nat_form

/-- Row record: reused alignment assets vs the consumer interface. -/
def tauCetiAlignmentRows : List (String × String × String) :=
  [ ("radical aliases (statement / UFM / natRadical)", "REUSED PROVED", "AbcStatementAlignmentActual.radical_eq_ufm + LogarithmicBoundEquivalence.radical_eq_natRadical")
  , ("Tau Ceti nat form", "REUSED PROVED", "AbcStatementAlignmentActual.tauCeti_nat_form")
  , ("our ABC <=> Tau Ceti ABC", "REUSED PROVED", "AbcStatementAlignmentActual.abcConjecture_iff_tauCeti")
  , ("Tau Ceti <=> log form", "COMPOSED PROVED", "tauCeti_iff_abcLogConjecture")
  , ("radical alias consumer", "COMPOSED PROVED", "radical_aliases_consumer") ]

theorem tauCetiAlignmentRows_length : tauCetiAlignmentRows.length = 5 := rfl

#check tauCeti_iff_abcLogConjecture
#check radical_aliases_consumer
#check tauCeti_nat_form_consumer
#check tauCetiAlignmentRows_length

end LeanFormal.IUT.XiFPaper.ShehddTauCetiAlignmentConsumerActualAdapted
end
