import tmp.sheaf.xif.paper.Node09H1aCompactMaxPrincipalActual
import tmp.sheaf.xif.paper.Node09H1aGenericCoordinateActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorLogShellHull
import tmp.sheaf.xif.paper.Mzk1P5ActualPacketTable
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Node09H1aCompactnessActual
open LeanFormal.IUT.LocalFieldProductHull
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.Mzk1P5ActualPacketTable
open LeanFormal.IUT.XiFPaper.Mzk1P5GammaSubsetHullActual
open LeanFormal.IUT.XiFPaper.Node09H1aCompactMaxPrincipalActual
open LeanFormal.IUT.XiFPaper.Node09H1aGenericCoordinateActual
variable {p : Nat} [Fact p.Prime] {ι : Type} [Fintype ι]
variable (A : ι → Type) [∀ i, NormedField (A i)]
variable [∀ i, NormedAlgebra ℚ_[p] (A i)] [∀ i, FiniteDimensional ℚ_[p] (A i)]
variable [∀ i, CharZero (A i)] [∀ i, IsUltrametricDist (A i)]
variable [∀ i, CompleteSpace (A i)] [∀ i, ProperSpace (A i)]
variable {J : Type} [Fintype J] {E : J → Type}
variable [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)] [∀ j, IsUltrametricDist (E j)]
variable [MeasurableSpace ((j : J) → E j)]
local instance piAlgebra : Algebra ℚ_[p] ((j : J) → E j) := Pi.algebra _ _
/-- gammaP5 is the compact tensor log-shell hull. -/
theorem isCompact_gammaP5_finiteSourceImage
    (e : FinitePadicTensor (p := p) (M := A) ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    IsCompact (gammaP5 (fun j => ⟨fun x y => IsUltrametricDist.norm_add_le_max x y⟩)
      (finiteSourceImage A e)) := by
  rw [gammaP5, integralSpan_tensorLogShellProductImage_eq_hull A e]
  exact isCompact_tensorLogShellHull A e
/-- The coordinate projection of gammaP5 is compact. -/
theorem isCompact_coordSubmodule
    (hna : ∀ j, IsNonarchimedean (Norm.norm : E j → ℝ))
    (M : Submodule (integralRing hna) ((j : J) → E j))
    (hM : IsCompact (M : Set ((j : J) → E j))) (j : J) :
    IsCompact (coordSubmodule hna M j : Set (E j)) := by
  have himg : (coordSubmodule hna M j : Set (E j)) =
      (fun x : (j : J) → E j => x j) '' (M : Set ((j : J) → E j)) := rfl
  rw [himg]
  exact hM.image (continuous_apply j)
#check isCompact_gammaP5_finiteSourceImage
#check isCompact_coordSubmodule
end LeanFormal.IUT.XiFPaper.Node09H1aCompactnessActual
end