import tmp.sheaf.xif.paper.S2797TensorLatticeSubsetAllRegionActual
import tmp.sheaf.xif.paper.S2736dTLCompactActual
import tmp.sheaf.xif.paper.S2744PerPlaceRegionAllCoordsActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2798TensorLatticeMeasureLeRegionActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.S2726PerPlaceUpdateRegionActual
open LeanFormal.IUT.XiFPaper.S2744PerPlaceRegionAllCoordsActual
open LeanFormal.IUT.XiFPaper.S2736cTensorLatticeActual
open LeanFormal.IUT.XiFPaper.S2736dTLCompactActual
open LeanFormal.IUT.XiFPaper.S2797TensorLatticeSubsetAllRegionActual

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
variable (M : ι → Type*) [∀ i, NormedAddCommGroup (M i)]
variable [∀ i, NormedSpace ℚ_[p] (M i)]
variable [∀ i, FiniteDimensional ℚ_[p] (M i)]
variable [∀ i, NeZero (Module.finrank ℚ_[p] (M i))]
variable [DecidableEq ι]

local instance measT : MeasurableSpace (FinitePadicTensor (p := p) M) := borel _
local instance borelT : BorelSpace (FinitePadicTensor (p := p) M) := ⟨rfl⟩

theorem tensorLattice_measure_le_regionAll
    (rho : ι → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (μ : Measure (FinitePadicTensor (p := p) M)) :
    μ (tensorLattice (p := p) M) ≤ μ (S2726PerPlaceUpdateRegionAll (p := p) M rho) :=
  measure_mono (tensorLattice_subset_regionAll (p := p) (M := M) rho hρ)

#check tensorLattice_measure_le_regionAll
end LeanFormal.IUT.XiFPaper.S2798TensorLatticeMeasureLeRegionActual
end
