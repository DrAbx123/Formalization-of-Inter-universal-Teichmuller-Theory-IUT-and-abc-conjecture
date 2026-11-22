/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.Geometry.LocalReduction
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import TateCurvesTheta.Converse.ReductionType
import Mathlib.Tactic

/-! # Mzk1SplitPredicateBridgeActual — split-reduction predicate bridge (A826, qpilot)

Field correspondence (LeanFormal vs vendor `TateCurvesTheta`):

| LeanFormal | vendor |
|---|---|
| `Completion place := (underlyingPrime place).adicCompletion K` | `K` with `»K‖` |
| `CompletionIntegers place = adicCompletionIntegers K` | `integerRing K = {x // »x‖ ≤ 1}` |
| `HasSplitMultiplicativeReductionOnMinimalModel R W` = `∃ C, (C • W).HasSplitMultiplicativeReduction R` (Mathlib class: minimal + valuative conditions + splitting polynomial) | `HasSplitMultiplicativeReduction W` = `∃ C h, (reduction (C•W) h).IsSplitMultiplicative` (vendor nodal-normalized structure) |
| `HasMultiplicativeReductionOnMinimalModel` | (vendor has no separate multiplicative predicate) |

Results:
1. `hasMultiplicativeReductionAt_iff_minimalModel` / `hasSplitMultiplicativeReductionAt_iff_minimalModel`:
   the named LeanFormal predicates are definitionally the minimal-model predicates at
   `CompletionIntegers place` / `Completion place` (the abbreviations unfold by `rfl`).
2. `vendor_split_of_j_gamma`: **the logical bridge**: if `1 < ‖W.j‖` and `γ(W)` is a
   square (plus `12 ≠ 0`), then `W` has vendor split multiplicative reduction
   (`TateCurvesTheta.hasSplitMultiplicativeReduction_iff`).
3. `vendor_split_of_leanformal`: composition on the actual LeanFormal predicate, with the
   two invariant hypotheses left explicit.

Remaining TRUE gap (precisely): derive `1 < ‖W.j‖` and `IsSquare (γ W)` from the Mathlib
class `W.HasSplitMultiplicativeReduction (CompletionIntegers place)` — this needs
(a) the valuation/norm dictionary for `CompletionIntegers place`
(`valuation K 𝔪 x = 1` ↦ `‖x‖ = 1`, `valuation K 𝔪 Δ < 1` ↦ `‖Δ‖ > 1` etc.) and
(b) lifting a residue root of the splitting polynomial to a square of `γ`, i.e. the
vendor equivalence between the Mathlib splitting condition and its nodal-normalized
`IsSplitMultiplicative` structure.  The (iii) point uniformization stays PENDING.

No axiom, no sorry, no `True` placeholder. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1SplitPredicateBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {F : Type u} [Field F] [NumberField F]

/-! ### 1. Named predicates are the minimal-model predicates (defeq) -/

theorem hasMultiplicativeReductionAt_iff_minimalModel
    (X : PuncturedEllipticCurve F) (place : NumberField.FinitePlace F) :
    X.HasMultiplicativeReductionAt place ↔
      HasMultiplicativeReductionOnMinimalModel (CompletionIntegers place)
        (X.curve.baseChange (Completion place)) := Iff.rfl

theorem hasSplitMultiplicativeReductionAt_iff_minimalModel
    (X : PuncturedEllipticCurve F) (place : NumberField.FinitePlace F) :
    X.HasSplitMultiplicativeReductionAt place ↔
      HasSplitMultiplicativeReductionOnMinimalModel (CompletionIntegers place)
        (X.curve.baseChange (Completion place)) := Iff.rfl

/-! ### 2. The logical bridge: j-norm and square γ give vendor split reduction -/

section LogicalBridge

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem vendor_split_of_j_gamma (W : WeierstrassCurve K) [W.IsElliptic]
    (h12 : (12 : K) ≠ 0)
    (hj : 1 < ‖W.j‖) (hγ : IsSquare (TateCurvesTheta.gammaInvariant W)) :
    TateCurvesTheta.HasSplitMultiplicativeReduction W :=
  (TateCurvesTheta.hasSplitMultiplicativeReduction_iff h12 W).mpr ⟨hj, hγ⟩

end LogicalBridge

/-! ### 3. Composition on the LeanFormal predicate -/

/-- Characteristic zero of the completed number field (local copy; the same statement
is in `Mzk1TateInstanceCoherenceActual`). -/
instance completionCharZero' (place : NumberField.FinitePlace F) :
    CharZero (Completion place) where
  cast_injective := by
    intro m n h
    have h' : (m : F) = (n : F) := by
      apply (algebraMap F (Completion place)).injective
      simpa only [map_natCast] using h
    exact Nat.cast_injective h'

section Composition

variable (place : NumberField.FinitePlace F)
variable [IsUltrametricDist (Completion place)] [CompleteSpace (Completion place)]

theorem vendor_split_of_leanformal
    (X : PuncturedEllipticCurve F)
    (hEll : (X.curve.baseChange (Completion place)).IsElliptic)
    (hj : 1 < ‖(X.curve.baseChange (Completion place)).j‖)
    (hγ : IsSquare (TateCurvesTheta.gammaInvariant
      (X.curve.baseChange (Completion place)))) :
    TateCurvesTheta.HasSplitMultiplicativeReduction
      (X.curve.baseChange (Completion place)) := by
  have h12 : (12 : Completion place) ≠ 0 := by
    haveI := completionCharZero' place
    norm_num
  exact vendor_split_of_j_gamma (W := X.curve.baseChange (Completion place)) h12 hj hγ

end Composition

/-! ### 4. Rows -/

def splitBridgeRows : List (String × String) :=
  [ ("LeanFormal named reductions = minimal-model predicates at Completion(Integers) place", "PROVED (defeq)"),
    ("Completion place = underlyingPrime.adicCompletion K", "DEFEQ (abbrev)"),
    ("vendor HasSplitMultiplicativeReduction from (j-norm > 1, square γ)", "PROVED"),
    ("composition on the LeanFormal predicate", "PROVED (given j/γ invariants)"),
    ("derive ‖j‖ > 1 and IsSquare γ from the Mathlib minimal-model class", "MISSING (valuation dictionary + root lifting)"),
    ("ring identification CompletionIntegers place vs vendor integerRing", "MISSING (subtype predicates)"),
    ("(iii) TatePointComparison point uniformization", "MISSING (analytic)") ]

theorem splitBridgeRows_length : splitBridgeRows.length = 7 := rfl

#check hasSplitMultiplicativeReductionAt_iff_minimalModel
#check vendor_split_of_j_gamma
#check vendor_split_of_leanformal
#check splitBridgeRows_length

end LeanFormal.IUT.XiFPaper.Mzk1SplitPredicateBridgeActual
end
