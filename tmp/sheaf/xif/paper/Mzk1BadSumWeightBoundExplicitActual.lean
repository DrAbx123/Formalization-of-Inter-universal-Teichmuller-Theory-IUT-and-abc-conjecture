/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Gap2ArithmeticReductionActual
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport

/-!
# A691 explicit final named input: BadSumWeightBound in natRadical form (mainline)

* `arithmeticWeight_abc_eq_log_natRadical`: the exact relation
  `arithmeticWeight (abcRationalPoint a c) = Real.log ((natRadical (a*b*c) : ℕ) : ℝ)`
  on ABC triples (from `RationalPrimeSupport.lean`);
* `BadSumWeightBoundNat`: the fully explicit natural-number form
  `Σ_b e_b d_b log p_b <= (1+ε) log rad(a*b*c) + D`;
* `badSumWeightBound_iff_nat`: equivalence of the two formulations;
* `FinalNamedInput`: the single remaining named input, in explicit form.

ABC gate NOT passed; no canonical change. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1BadSumWeightBoundExplicitActual

open scoped Pointwise ENNReal BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarScalingOneDimActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1CorrectedGap1UnconditionalActual
open LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticReductionActual
open LeanFormal.IUT.XiFPaper.Mzk1CarrierBadInvScaleProductActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- Exact weight/radical relation on ABC triples. -/
theorem arithmeticWeight_abc_eq_log_natRadical {a b c : Nat} (habc : IsABCTriple a b c) :
    arithmeticWeight (abcRationalPoint a c) =
      Real.log ((natRadical (a * b * c) : ℕ) : ℝ) :=
  arithmeticWeight_abcRationalPoint habc

/-- The remaining named input in fully explicit natural-number form. -/
def BadSumWeightBoundNat
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, ∀ aN bN cN : Nat, IsABCTriple aN bN cN →
    (∑ bBad : Bad (nativePlaceSelection T),
      (eN aN bN cN bBad : ℝ) *
        ((Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : ℝ) *
          Real.log ((qVFamTensorP T bBad : ℕ) : ℝ))) ≤
      (1 + ε) * Real.log ((natRadical (aN * bN * cN) : ℕ) : ℝ) + D

/-- The explicit final named input predicate. -/
def FinalNamedInput
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat) : Prop :=
  BadSumWeightBoundNat T eN

/-- The two formulations of the remaining named input are equivalent. -/
theorem badSumWeightBound_iff_nat
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat) :
    Mzk1Gap2ArithmeticReductionActual.BadSumWeightBound T eN ↔
      BadSumWeightBoundNat T eN := by
  constructor
  · intro h ε hε
    obtain ⟨D, hD⟩ := h ε hε
    refine ⟨D, ?_⟩
    intro aN bN cN habc
    have hD' := hD aN bN cN habc
    rw [arithmeticWeight_abc_eq_log_natRadical habc] at hD'
    exact hD'
  · intro h ε hε
    obtain ⟨D, hD⟩ := h ε hε
    refine ⟨D, ?_⟩
    intro aN bN cN habc
    have hD' := hD aN bN cN habc
    rw [arithmeticWeight_abc_eq_log_natRadical habc]
    exact hD'

theorem finalNamedInput_iff_badSumWeightBound
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat) :
    FinalNamedInput T eN ↔
      Mzk1Gap2ArithmeticReductionActual.BadSumWeightBound T eN :=
  (badSumWeightBound_iff_nat T eN).symm

/-- Scope rows of the explicit final named input. -/
def explicitRows : List (String × String) :=
  [ ("weight = log natRadical(a*b*c)", "PROVED (arithmeticWeight_abc_eq_log_natRadical)"),
    ("BadSumWeightBound <=> natRadical form", "PROVED (badSumWeightBound_iff_nat)"),
    ("FinalNamedInput", "named predicate = BadSumWeightBoundNat"),
    ("reverse (ABC => named input)", "NOT_PROVED (d_b coefficient obstruction)"),
    ("scope", "ABC gate NOT passed; no canonical change") ]

theorem explicitRows_length : explicitRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1BadSumWeightBoundExplicitActual

end

/-! ### Axiom gates (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1BadSumWeightBoundExplicitActual.arithmeticWeight_abc_eq_log_natRadical
#print axioms LeanFormal.IUT.XiFPaper.Mzk1BadSumWeightBoundExplicitActual.badSumWeightBound_iff_nat
#print axioms LeanFormal.IUT.XiFPaper.Mzk1BadSumWeightBoundExplicitActual.explicitRows_length