import tmp.sheaf.xif.paper.S2009DicksonActual
import tmp.sheaf.xif.paper.S2057DedekindFrobBridgeActual
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace LeanFormal.IUT.XiFPaper.S2613DetCyclotomicInterfaceActual

open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual

/-- Exact determinant-surjectivity gap on the actual range. -/
def S2613DetSurjectiveRemaining : Prop :=
  DetSurjectiveOn
    (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range

/-- Minimal cyclotomic compatibility interface: an actual multiplicative
character of the absolute Galois group whose values are the determinants and
which is surjective onto ZMod 5 units. -/
def S2613DetCyclotomicCompatibility : Prop :=
  ∃ χ : Gal(AlgebraicClosure S1720Field/S1720Field) →* (ZMod S1987Five.value)ˣ,
    Function.Surjective χ ∧
      ∀ (σ : Gal(AlgebraicClosure S1720Field/S1720Field)),
        Matrix.GeneralLinearGroup.det
          (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis σ) =
          χ σ


/-- The cyclotomic compatibility interface implies determinant surjectivity on
the actual range. -/
theorem S2613DetSurjective_of_compat
    (h : S2613DetCyclotomicCompatibility) :
    S2613DetSurjectiveRemaining := by
  intro a
  obtain ⟨χ, hsurj, hdet⟩ := h
  obtain ⟨σ, rfl⟩ := hsurj a
  refine ⟨S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis σ,
    ⟨σ, rfl⟩, ?_⟩
  exact hdet σ


#check S2613DetSurjectiveRemaining
#check S2613DetCyclotomicCompatibility

end LeanFormal.IUT.XiFPaper.S2613DetCyclotomicInterfaceActual
end