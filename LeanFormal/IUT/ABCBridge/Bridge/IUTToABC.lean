import LeanFormal.IUT.ABCBridge.Statement
import LeanFormal.IUT.ABCBridge.Arithmetic.LogarithmicBoundEquivalence
import LeanFormal.IUT.Audit.Status

/-! Tracked obligation for the eventual arithmetic bridge to ABC. -/

namespace LeanFormal.IUT.Audit

def cor312ToABCBridge : Obligation :=
  { id := "IUT-III.cor312-to-ABC"
    source := "IUT III Corollary 3.12; IUT IV downstream estimates"
    status := VerificationStatus.pending
    note :=
      "The arithmetic reduction target shape is packaged in " ++
        "`LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCCards`: chain-step cards step-1/2/3 and " ++
        "the statement-only shape `explicitEstimatesThm54Shape`; the independent " ++
        "obligation `IUT-III.cor312-to-ABC-chain-cards` remains pending there. " ++
        "The proved interface theorem `cor312ToABCTargetShape_iff_abcConjecture` " ++
        "identifies the target shape with `ABCConjecture` using only the standard " ++
        "three axioms. What remains for this obligation is the arithmetic estimate." }

end LeanFormal.IUT.Audit

namespace LeanFormal.IUT

/--
The standard radical-power `ABCConjecture` is equivalent to its logarithmic
form: for every `epsilon > 0` there is an additive constant `A` with
`log c <= (1 + epsilon) * log (radical (a*b*c)) + A` on all ABC triples.

This is the exact arithmetic reduction from the additive logarithmic estimates
produced on the IUT side to the multiplicative `ABCInequality` of
`ABCConjecture`.  It is an equivalence of the two quantified statements; no
ABC estimate is assumed on either side.
-/
theorem abcConjecture_iff_abcLogConjecture :
    ABCConjecture ↔ ABCLogConjecture := by
  constructor
  · intro h epsilon heps
    obtain ⟨K, hK, hKbound⟩ := h epsilon heps
    refine (abcLogBound_exists_iff_rpow_exists epsilon heps).mpr ⟨K, hK, ?_⟩
    intro a b c habc
    have h := hKbound a b c habc
    rwa [ABCInequality] at h
  · intro h epsilon heps
    obtain ⟨A, hA⟩ := h epsilon heps
    obtain ⟨K, hK, hKrpow⟩ := (abcLogBound_exists_iff_rpow_exists epsilon heps).mp ⟨A, hA⟩
    exact ⟨K, hK, fun a b c habc => by
      rw [ABCInequality]
      exact hKrpow a b c habc⟩

/--
The standard radical-power `ABCConjecture` is equivalent to the arithmetic-weight height
form: for every `epsilon > 0` there is an additive constant `A` with
`logHeight₁ (abcRationalPoint a c) <= (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A`
on all ABC triples.

Here `Height.logHeight₁ (abcRationalPoint a c)` is the IUT height of the compiled rational
point and `arithmeticWeight (abcRationalPoint a c)` is the sibling weight; the two radicals
agree on ABC triples by `radical_log_eq_arithmeticWeight`.  The constant depends only on
`epsilon`, and all objects and the quantifier order are the actual ones.  This is the
arithmetic interface for a future geometric/IUT estimate, not a proof of that estimate.
-/
theorem abcConjecture_iff_abcArithmeticWeightHeightBound :
    ABCConjecture ↔
      (∀ epsilon : Real, 0 < epsilon → ∃ A : Real,
        ∀ a b c : Nat, IsABCTriple a b c →
          Height.logHeight₁ (abcRationalPoint a c) ≤
            (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A) := by
  rw [abcConjecture_iff_abcLogConjecture]
  simp only [ABCLogConjecture, ABCLogBound]
  constructor
  · intro h epsilon heps
    obtain ⟨A, hA⟩ := h epsilon heps
    refine ⟨A, ?_⟩
    intro a b c habc
    have hle := hA a b c habc
    rw [abcRationalPoint_logHeight₁ habc, ← radical_log_eq_arithmeticWeight habc]
    exact hle
  · intro h epsilon heps
    obtain ⟨A, hA⟩ := h epsilon heps
    refine ⟨A, ?_⟩
    intro a b c habc
    have hle := hA a b c habc
    rw [← abcRationalPoint_logHeight₁ habc, radical_log_eq_arithmeticWeight habc]
    exact hle

end LeanFormal.IUT
