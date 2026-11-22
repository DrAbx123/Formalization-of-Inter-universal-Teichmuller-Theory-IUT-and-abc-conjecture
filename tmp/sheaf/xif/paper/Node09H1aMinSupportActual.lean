import tmp.sheaf.xif.paper.Node09H1bVolumeActual
import tmp.sheaf.xif.paper.Node09H1aSourceVectorsActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Node09H1aMinSupportActual
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.Mzk1P5ActualPacketTable
open LeanFormal.IUT.XiFPaper.Node09H1aSourceVectorsActual
open LeanFormal.IUT.XiFPaper.Node09H1bVolumeActual

variable {p : Nat} [Fact p.Prime] {ι : Type} [Fintype ι]
variable (A : ι → Type) [∀ i, NormedField (A i)]
variable [∀ i, NormedAlgebra ℚ_[p] (A i)] [∀ i, FiniteDimensional ℚ_[p] (A i)]
variable [∀ i, CharZero (A i)] [∀ i, IsUltrametricDist (A i)]
variable [∀ i, CompleteSpace (A i)] [∀ i, ProperSpace (A i)]
variable {J : Type} [Fintype J] {E : J → Type}
variable [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)] [∀ j, IsUltrametricDist (E j)]
variable [∀ j, CharZero (E j)] [∀ j, CompleteSpace (E j)] [∀ j, ProperSpace (E j)]
variable [MeasurableSpace ((j : J) → E j)]

/-- An actual source vector attaining the coordinatewise minimum valuation
`rP5` at coordinate `j`. -/
noncomputable def minSourceVector
    (e : FinitePadicTensor (p := p) (M := A) ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (basis : Module.Basis (FinitePadicTensorIndex (p := p) A) ℚ_[p]
      (FinitePadicTensor (p := p) A))
    (hne : (Finset.univ : Finset (FinitePadicTensorIndex (p := p) A)).Nonempty)
    (j : J) : (j : J) → E j :=
  sourceVector A e basis
    (Classical.choose (rP5_eq_sourceFactorValuation A e basis hne j))

/-- The minimum source vector has the minimal valuation `rP5`. -/
theorem minSourceVector_valuation_eq_rP5
    (e : FinitePadicTensor (p := p) (M := A) ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (basis : Module.Basis (FinitePadicTensorIndex (p := p) A) ℚ_[p]
      (FinitePadicTensor (p := p) A))
    (hne : (Finset.univ : Finset (FinitePadicTensorIndex (p := p) A)).Nonempty)
    (j : J) :
    sourceFactorValuation A e basis
        (Classical.choose (rP5_eq_sourceFactorValuation A e basis hne j)) j =
      rP5 A e basis hne j := by
  exact (Classical.choose_spec (rP5_eq_sourceFactorValuation A e basis hne j)).symm

/-- The minimum source vector lies in the actual finite source image. -/
theorem minSourceVector_mem_finiteSourceImage
    (e : FinitePadicTensor (p := p) (M := A) ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (basis : Module.Basis (FinitePadicTensorIndex (p := p) A) ℚ_[p]
      (FinitePadicTensor (p := p) A))
    (hbasis : ∀ k, basis k ∈ tensorLogShellRegion (p := p) A)
    (hne : (Finset.univ : Finset (FinitePadicTensorIndex (p := p) A)).Nonempty)
    (j : J) :
    minSourceVector A e basis hne j ∈ finiteSourceImage A e :=
  sourceVector_mem_finiteSourceImage A e basis hbasis _

#print axioms minSourceVector
#print axioms minSourceVector_valuation_eq_rP5
#print axioms minSourceVector_mem_finiteSourceImage
end LeanFormal.IUT.XiFPaper.Node09H1aMinSupportActual