import tmp.sheaf.xif.paper.Mzk1Gap2ArithmeticReductionActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi natRadical explicit form of BadSumWeightBound

Explicit `natRadical a b c = radical (a*b*c)` formulation of the bad-sum weight
bound, with equivalence to the arithmeticWeight form under the radical-log
dictionary identity. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXINatRadicalBadSumV3Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticReductionActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- Explicit natural radical of an ABC triple. -/
def natRadical (a b c : Nat) : Nat := radical (a * b * c)

/-- The bad-sum weight bound with the RHS written through `natRadical`. -/
def BadSumWeightBoundNatRadical
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, ∀ aN bN cN : Nat, IsABCTriple aN bN cN →
    (∑ bBad : Bad (nativePlaceSelection T),
      (eN aN bN cN bBad : ℝ) *
        ((Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : ℝ) *
          Real.log ((qVFamTensorP T bBad : ℕ) : ℝ))) ≤
      (1 + ε) * Real.log (natRadical aN bN cN : ℝ) + D

theorem badSumWeightBound_iff_natRadical
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat)
    (hdict : ∀ a b c : Nat, IsABCTriple a b c →
      arithmeticWeight (abcRationalPoint a c) = Real.log (natRadical a b c : ℝ)) :
    BadSumWeightBound T eN ↔ BadSumWeightBoundNatRadical T eN := by
  constructor
  · intro h ε hε
    obtain ⟨D, hD⟩ := h ε hε
    refine ⟨D, fun a b c habc => ?_⟩
    have hw := hdict a b c habc
    have := hD a b c habc
    simpa [← hw] using this
  · intro h ε hε
    obtain ⟨D, hD⟩ := h ε hε
    refine ⟨D, fun a b c habc => ?_⟩
    have hw := hdict a b c habc
    have := hD a b c habc
    simpa [hw] using this

end LeanFormal.IUT.XiFPaper.Mzk1StepXINatRadicalBadSumV3Actual

end
