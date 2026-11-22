import tmp.sheaf.xif.paper.Mzk1P5ActualPacketTable
import tmp.sheaf.xif.paper.Mzk1P5GammaSubsetHullActual
import Mathlib.MeasureTheory.Measure.Haar.Basic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P5OTVolumeFinal5Actual
open MeasureTheory
open LeanFormal.IUT.LocalFieldProductHull
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.Mzk1P5ActualPacketTable
open LeanFormal.IUT.XiFPaper.Mzk1P5GammaSubsetHullActual
variable {p : Nat} [Fact p.Prime] {ι : Type} [Fintype ι]
variable (A : ι → Type) [∀ i, NormedField (A i)]
variable [∀ i, NormedAlgebra ℚ_[p] (A i)] [∀ i, FiniteDimensional ℚ_[p] (A i)]
variable [∀ i, CharZero (A i)] [∀ i, IsUltrametricDist (A i)]
variable [∀ i, CompleteSpace (A i)] [∀ i, ProperSpace (A i)]
variable {J : Type} [Fintype J] {E : J → Type}
variable [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)] [∀ j, IsUltrametricDist (E j)]
variable [MeasurableSpace ((j : J) → E j)]
local instance piAlgebra : Algebra ℚ_[p] ((j : J) → E j) := Pi.algebra _ _
def actualNormalizedLogVolume
    (e : FinitePadicTensor (p := p) (M := A) ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (hna : ∀ j, IsNonarchimedean (Norm.norm : E j → ℝ))
    (μ : Measure ((j : J) → E j)) : Real :=
  Real.log (μ ((gammaP5 hna (finiteSourceImage A e)) : Set ((j : J) → E j))).toReal -
    Real.log (μ ((unitReferenceLattice (E := E) hna) : Set ((j : J) → E j))).toReal
#check actualNormalizedLogVolume
end LeanFormal.IUT.XiFPaper.Mzk1P5OTVolumeFinal5Actual
end