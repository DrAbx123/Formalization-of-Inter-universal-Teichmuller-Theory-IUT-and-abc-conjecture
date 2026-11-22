import tmp.sheaf.xif.paper.Mzk1Gap2ArithmeticReductionActual
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport

/-! # Mzk1Stage4BadSumNatRadicalActual (stage4 lane; BadSumWeightBound natRadical form)

A690 module: EXPLICIT `natRadical` form of the remaining named input.  Using the green
`RationalPrimeSupport` theorem `arithmeticWeight_abcRationalPoint`, the named arithmetic
bound `BadSumWeightBound` is equivalently stated with the project radical:
`Σ_b e_b d_b log p_b ≤ (1+ε)·log(natRadical(a·b·c)) + D'`.
This is the precise relation announced for the named input; it does NOT prove the input
and the ABC gate is NOT passed.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4BadSumNatRadicalActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticReductionActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- `BadSumWeightBound` with the arithmetic weight made explicit via the project
radical `natRadical(a·b·c)`. -/
theorem badSumWeightBound_natRadical_iff
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat) :
    BadSumWeightBound T eN ↔
      ∀ ε : Real, 0 < ε → ∃ D : Real,
        ∀ aN bN cN : Nat, IsABCTriple aN bN cN →
          (∑ bBad : Bad (nativePlaceSelection T),
            (eN aN bN cN bBad : Real) *
              ((Module.finrank ℚ_[(qVFamTensorP T bBad)]
                (rootNormedExtension T bBad) : Real) *
                Real.log ((qVFamTensorP T bBad : Nat) : Real))) ≤
            (1 + ε) * Real.log (natRadical (aN * bN * cN) : Real) + D := by
  unfold BadSumWeightBound
  constructor
  · intro h ε hε
    obtain ⟨D, hD⟩ := h ε hε
    refine ⟨D, fun aN bN cN habc => ?_⟩
    have h' := hD aN bN cN habc
    rwa [arithmeticWeight_abcRationalPoint habc] at h'
  · intro h ε hε
    obtain ⟨D, hD⟩ := h ε hε
    refine ⟨D, fun aN bN cN habc => ?_⟩
    have h' := hD aN bN cN habc
    rwa [arithmeticWeight_abcRationalPoint habc]

/-- The named-input ledger row with the radical form (explicit). -/
def namedInputRows : List (String × String) :=
  [ ("corrected-region Gap2 shape", "named input (⇔ BadSumWeightBound by correctedGap2_iff_arith)")
  , ("arithmeticWeight", "= log(natRadical(a·b·c)) at abcRationalPoint (green RationalPrimeSupport)")
  , ("named bound, radical form", "Σ_b e_b d_b log p_b ≤ (1+ε)·log(natRadical(a·b·c)) + D'")
  , ("status", "NAMED (not proved); ABC gate NOT passed; no canonical change")
  ]

/-- The named-input record has four rows. -/
theorem namedInputRows_length : namedInputRows.length = 4 := rfl

#print axioms badSumWeightBound_natRadical_iff
#check badSumWeightBound_natRadical_iff
#check namedInputRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Stage4BadSumNatRadicalActual
end
