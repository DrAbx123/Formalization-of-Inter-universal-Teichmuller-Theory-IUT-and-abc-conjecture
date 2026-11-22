import LeanFormal.IUT.ABCBridge.Arithmetic.LogarithmicBoundEquivalence
import LeanFormal.IUT.ABCBridge.Bridge.IUTToABC

/-!
# ShehddABCLogBoundFormActualAdapted — ABC log-bound / radical-power form consumer

STEP 0 prior-art (reuse only):
* ABCBridge/Arithmetic/LogarithmicBoundEquivalence.lean: ABCLogConjecture, ABCLogBound,
  abcLogBound_exists_iff_rpow_exists, radical_log_eq_arithmeticWeight, abcTriple_c_pos;
* ABCBridge/Bridge/IUTToABC.lean: abcConjecture_iff_abcLogConjecture.

This file exposes the radical-power form of ABC as a consumer: the log form is equivalent
to the c <= K * radical^(1+epsilon) form, hence ABCConjecture itself has that form.  No
new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddABCLogBoundFormActualAdapted

open LeanFormal.IUT

/-- **PROVED consumer:** per-epsilon log form <=> radical-power form with positive K. -/
theorem abcLogBound_rpow_consumer (epsilon : ℝ) (heps : 0 < epsilon) :
    (∃ A : ℝ, ABCLogBound epsilon A) ↔
      (∃ K : ℝ, 0 < K ∧
        ∀ a b c : Nat, IsABCTriple a b c →
          (c : ℝ) ≤ K * (radical (a * b * c) : ℝ) ^ (1 + epsilon)) :=
  abcLogBound_exists_iff_rpow_exists epsilon heps

/-- **PROVED consumer:** ABCLogConjecture in the radical-power form. -/
theorem abcLogConjecture_iff_rpow :
    ABCLogConjecture ↔
      (∀ epsilon : ℝ, 0 < epsilon →
        ∃ K : ℝ, 0 < K ∧
          ∀ a b c : Nat, IsABCTriple a b c →
            (c : ℝ) ≤ K * (radical (a * b * c) : ℝ) ^ (1 + epsilon)) := by
  constructor
  · intro h epsilon hepsilon
    exact (abcLogBound_exists_iff_rpow_exists epsilon hepsilon).mp (h epsilon hepsilon)
  · intro h epsilon hepsilon
    exact (abcLogBound_exists_iff_rpow_exists epsilon hepsilon).mpr (h epsilon hepsilon)

/-- **PROVED consumer:** ABCConjecture in the radical-power form. -/
theorem abcConjecture_iff_rpow :
    ABCConjecture ↔
      (∀ epsilon : ℝ, 0 < epsilon →
        ∃ K : ℝ, 0 < K ∧
          ∀ a b c : Nat, IsABCTriple a b c →
            (c : ℝ) ≤ K * (radical (a * b * c) : ℝ) ^ (1 + epsilon)) :=
  abcConjecture_iff_abcLogConjecture.trans abcLogConjecture_iff_rpow

/-- **PROVED consumer:** on ABC triples, log radical = sibling arithmetic weight. -/
theorem radical_log_weight_consumer {a b c : Nat} (h : IsABCTriple a b c) :
    Real.log (radical (a * b * c) : ℝ) = arithmeticWeight (abcRationalPoint a c) :=
  radical_log_eq_arithmeticWeight h

/-- Row record: reused equivalences vs composed consumer forms. -/
def abcLogBoundFormRows : List (String × String × String) :=
  [ ("per-epsilon log form <=> radical-power form", "REUSED PROVED", "abcLogBound_exists_iff_rpow_exists")
  , ("radical log = arithmetic weight on ABC triples", "REUSED PROVED", "radical_log_eq_arithmeticWeight")
  , ("ABC <=> log form", "REUSED PROVED", "IUTToABC.abcConjecture_iff_abcLogConjecture")
  , ("ABCLogConjecture <=> radical-power form", "COMPOSED PROVED", "abcLogConjecture_iff_rpow")
  , ("ABCConjecture <=> radical-power form", "COMPOSED PROVED", "abcConjecture_iff_rpow") ]

theorem abcLogBoundFormRows_length : abcLogBoundFormRows.length = 5 := rfl

#check abcLogBound_rpow_consumer
#check abcLogConjecture_iff_rpow
#check abcConjecture_iff_rpow
#check radical_log_weight_consumer
#check abcLogBoundFormRows_length

end LeanFormal.IUT.XiFPaper.ShehddABCLogBoundFormActualAdapted
end
