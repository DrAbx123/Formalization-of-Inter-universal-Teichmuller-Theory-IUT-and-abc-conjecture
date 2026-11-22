import tmp.sheaf.xif.paper.S2744PerPlaceRegionAllCoordsActual

noncomputable section
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2751PerPlaceRegionAllBoundedActualAdapted

open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.S2726PerPlaceUpdateRegionActual
open LeanFormal.IUT.XiFPaper.S2744PerPlaceRegionAllCoordsActual

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
variable (M : ι → Type*) [∀ i, NormedAddCommGroup (M i)]
variable [∀ i, NormedSpace ℚ_[p] (M i)]
variable [∀ i, FiniteDimensional ℚ_[p] (M i)]
variable [∀ i, NeZero (Module.finrank ℚ_[p] (M i))]
variable [DecidableEq ι]

theorem isBounded_perPlaceUpdateRegionAll
    (rho : ι → ℝ) (hρ : ∀ i, 0 ≤ rho i) :
    Bornology.IsBounded (S2726PerPlaceUpdateRegionAll (p := p) M rho) :=
  (isCompact_perPlaceUpdateRegionAll (p := p) M rho hρ).isBounded

#check isBounded_perPlaceUpdateRegionAll
end LeanFormal.IUT.XiFPaper.S2751PerPlaceRegionAllBoundedActualAdapted
end
