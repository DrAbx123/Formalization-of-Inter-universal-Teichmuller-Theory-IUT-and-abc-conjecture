/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Gap2ArithmeticReductionActual
import LeanFormal.IUT.ABCBridge.Arithmetic.LogarithmicBoundEquivalence
import Mathlib.Tactic
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.S1929LiteralIQCarrierActual

/-! # Mzk1BadSumWeightRadicalQpilotActual — BadSumWeightBound with natRadical (A690)

Explicit natRadical form of the pure arithmetic `BadSumWeightBound`: the weight is
`Real.log (radical (a*b*c))` (the accepted dictionary identity
`radical_log_eq_arithmeticWeight` says it equals `arithmeticWeight (abcRationalPoint a c)`
on ABC triples).  The two forms are equivalent. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.Mzk1BadSumWeightRadicalQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticReductionActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [Nonempty (Bad (nativePlaceSelection T))]

/-- The pure arithmetic Gap-2 bound with the weight written as `log rad(abc)`. -/
def BadSumWeightBoundRadical
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat) : Prop :=
  ∀ epsilon : Real, 0 < epsilon → ∃ D : Real,
    ∀ aN bN cN : Nat, IsABCTriple aN bN cN →
      (∑ bBad : Bad (nativePlaceSelection T),
        (eN aN bN cN bBad : Real) *
          ((Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : Real) *
            Real.log ((qVFamTensorP T bBad : Nat) : Real))) ≤
        (1 + epsilon) * Real.log (radical (aN * bN * cN) : Real) + D

/-- `BadSumWeightBound` is equivalent to its explicit natRadical form. -/
theorem badSumWeightBound_iff_radical
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat) :
    BadSumWeightBound T eN ↔ BadSumWeightBoundRadical T eN := by
  constructor
  · intro h epsilon hepsilon
    obtain ⟨D, hD⟩ := h epsilon hepsilon
    refine ⟨D, fun aN bN cN habc => ?_⟩
    have h' := hD aN bN cN habc
    rwa [← radical_log_eq_arithmeticWeight habc] at h'
  · intro h epsilon hepsilon
    obtain ⟨D, hD⟩ := h epsilon hepsilon
    refine ⟨D, fun aN bN cN habc => ?_⟩
    have h' := hD aN bN cN habc
    rwa [radical_log_eq_arithmeticWeight habc] at h'

/-- Rows for the natRadical explicitization. -/
def badSumRadicalRows : List (String × String) :=
  [ ("BadSumWeightBound natRadical form", "DEFINED"),
    ("equivalence with arithmeticWeight form", "PROVED"),
    ("dictionary identity", "PROVED (radical_log_eq_arithmeticWeight)") ]

theorem badSumRadicalRows_length : badSumRadicalRows.length = 3 := rfl

#check badSumWeightBound_iff_radical
#check badSumRadicalRows_length

end LeanFormal.IUT.XiFPaper.Mzk1BadSumWeightRadicalQpilotActual
end
