import tmp.sheaf.xif.paper.Mzk1Gap2ArithmeticReductionActual
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport
import LeanFormal.IUT.ABCBridge.Statement
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# shehdd A690 BadSumWeightBound with explicit natRadical (Sha)

Explicit radical form of the corrected Gap2 arithmetic reduction:
* `arithmeticWeight_abcRationalPoint_eq_log_radical`: on ABC triples the arithmetic
  weight is the log of the radical `rad(a*b*c)`;
* `badSumWeightBound_radical_iff`: `BadSumWeightBound` is equivalent to the pure
  arithmetic inequality with `Real.log (rad(a*b*c))` on the right-hand side.

No gap is proved; the arithmetic inequality remains the named input.
No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1BadSumWeightRadicalShaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarScalingOneDimActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticReductionActual

/-- On ABC triples, `arithmeticWeight` is the log of the natRadical of `a*b*c`. -/
theorem arithmeticWeight_abcRationalPoint_eq_log_radical {a b c : Nat}
    (h : IsABCTriple a b c) :
    arithmeticWeight (abcRationalPoint a c) =
      Real.log ((radical (a * b * c) : Nat) : Real) := by
  unfold arithmeticWeight
  rw [arithmeticPrimeSupport_abcRationalPoint h]
  rw [← natRadical_cast_log_eq_sum_primeFactors (a * b * c)]

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- `BadSumWeightBound` in explicit natRadical form. -/
theorem badSumWeightBound_radical_iff
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat) :
    BadSumWeightBound T eN ↔
      ∀ ε : Real, 0 < ε → ∃ D : Real,
        ∀ a b c : Nat, IsABCTriple a b c →
          (∑ bBad : Bad (nativePlaceSelection T),
            (eN a b c bBad : Real) *
              ((Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : Real) *
                Real.log ((qVFamTensorP T bBad : ℕ) : Real))) ≤
            (1 + ε) * Real.log ((radical (a * b * c) : Nat) : Real) + D := by
  constructor
  · intro h ε hε
    obtain ⟨D, hD⟩ := h ε hε
    refine ⟨D, fun a b c habc => ?_⟩
    rw [← arithmeticWeight_abcRationalPoint_eq_log_radical habc]
    exact hD a b c habc
  · intro h ε hε
    obtain ⟨D, hD⟩ := h ε hε
    refine ⟨D, fun a b c habc => ?_⟩
    rw [arithmeticWeight_abcRationalPoint_eq_log_radical habc]
    exact hD a b c habc

structure RadicalRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def radicalRows : List RadicalRow :=
  [ ⟨"weight = log radical", "arithmeticWeight_abcRationalPoint_eq_log_radical", "GREEN"⟩
  , ⟨"BadSumWeightBound radical form", "badSumWeightBound_radical_iff", "GREEN_EQUIV"⟩
  , ⟨"remaining named input", "BadSumWeightBound arithmetic inequality", "NAMED"⟩
  , ⟨"scope", "explicitization only; no gap claimed", "INTEGRITY"⟩
  ]

theorem radicalRows_length : radicalRows.length = 4 := rfl

theorem radicalRows_statuses_ok :
    radicalRows.all (fun r =>
      r.status ∈ ["GREEN", "GREEN_EQUIV", "NAMED", "INTEGRITY"]) = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1BadSumWeightRadicalShaActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1BadSumWeightRadicalShaActual.arithmeticWeight_abcRationalPoint_eq_log_radical
#print axioms LeanFormal.IUT.XiFPaper.Mzk1BadSumWeightRadicalShaActual.badSumWeightBound_radical_iff
