import tmp.sheaf.xif.paper.S2744PerPlaceRegionAllCoordsActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2799RegionAllClosedCompactActual

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


theorem regionAll_closed_and_compact
    (rho : ι → ℝ) (hρ : ∀ i, 0 ≤ rho i) :
    IsClosed (S2726PerPlaceUpdateRegionAll (p := p) M rho) ∧
      IsCompact (S2726PerPlaceUpdateRegionAll (p := p) M rho) :=
  ⟨isClosed_perPlaceUpdateRegionAll (p := p) M rho hρ,
    isCompact_perPlaceUpdateRegionAll (p := p) M rho hρ⟩

#check regionAll_closed_and_compact

end LeanFormal.IUT.XiFPaper.S2799RegionAllClosedCompactActual
end
