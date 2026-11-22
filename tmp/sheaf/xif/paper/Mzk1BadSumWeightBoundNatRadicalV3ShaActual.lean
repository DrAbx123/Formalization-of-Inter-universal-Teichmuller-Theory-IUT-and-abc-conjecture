import tmp.sheaf.xif.paper.Mzk1Gap2ArithmeticReductionActual
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport

/-! # BadSumWeightBound with explicit natRadical (V3) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1BadSumWeightBoundNatRadicalV3ShaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticReductionActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

noncomputable def badSum
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat)
    (a b c : Nat) : Real :=
  ∑ bBad : Bad (nativePlaceSelection T),
    (eN a b c bBad : Real) *
      ((Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : Real) *
        Real.log ((qVFamTensorP T bBad : Nat) : Real))

/-- Pure arithmetic BadSumWeightBound with explicit `natRadical(a*b*c)`. -/
def BadSumWeightBoundNatRadical
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat) : Prop :=
  forall epsilon : Real, 0 < epsilon → exists D : Real,
    forall aN bN cN : Nat, IsABCTriple aN bN cN →
      badSum T eN aN bN cN ≤
        (1 + epsilon) * Real.log (natRadical (aN * bN * cN) : Real) + D

theorem badSumWeightBound_iff_natRadical
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat) :
    BadSumWeightBound T eN ↔ BadSumWeightBoundNatRadical T eN := by
  constructor
  · intro h epsilon hepsilon
    obtain ⟨D, hD⟩ := h epsilon hepsilon
    refine ⟨D, ?_⟩
    intro a b c habc
    have h := hD a b c habc
    rw [arithmeticWeight_abcRationalPoint habc] at h
    simpa [badSum] using h
  · intro h epsilon hepsilon
    obtain ⟨D, hD⟩ := h epsilon hepsilon
    refine ⟨D, ?_⟩
    intro a b c habc
    have h := hD a b c habc
    rw [arithmeticWeight_abcRationalPoint habc]
    simpa [badSum] using h

#print axioms badSumWeightBound_iff_natRadical

end LeanFormal.IUT.XiFPaper.Mzk1BadSumWeightBoundNatRadicalV3ShaActual
