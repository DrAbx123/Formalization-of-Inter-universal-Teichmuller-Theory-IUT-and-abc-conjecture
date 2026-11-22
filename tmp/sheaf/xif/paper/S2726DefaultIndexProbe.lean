import Mathlib
import tmp.sheaf.xif.paper.S2726TensorComparisonRegionRhoActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldPadicTensor

namespace LeanFormal.IUT.XiFPaper.S2726DefaultIndexProbe

universe u
variable {p : Nat} [Fact p.Prime] {ι : Type u} [Fintype ι] [DecidableEq ι]
variable (M : ι → Type u) [∀ i, NormedAddCommGroup (M i)]
variable [∀ i, NormedSpace ℚ_[p] (M i)]
variable [∀ i, FiniteDimensional ℚ_[p] (M i)]
variable [∀ i, Nontrivial (M i)]

#check Module.finrank_pos
#check NeZero
#check Function.update
#check Function.update_self
#check Function.update_of_ne
#check Function.update_apply

/-- A default global tensor index: at each place choose the zero coordinate. -/
noncomputable def defaultTensorIndex : FinitePadicTensorIndex (p := p) M :=
  fun i => ⟨0, Module.finrank_pos (R := ℚ_[p]) (M := M i)⟩

#check defaultTensorIndex

/-- NeZero instance for the per-place coordinate dimension, derived from
Module.finrank_pos. -/
theorem finrank_neZero (i : ι) : NeZero (Module.finrank ℚ_[p] (M i)) :=
  ⟨Nat.pos_iff_ne_zero.mp (Module.finrank_pos (R := ℚ_[p]) (M := M i))⟩

#check finrank_neZero

/-- The per-place default-index region statement. -/
theorem perPlaceDefaultRegion_target
    (y : FinitePadicTensorIndex (p := p) M → ℚ_[p])
    (rho : ι → Real) (d : FinitePadicTensorIndex (p := p) M)
    (h : ∀ (i : ι) (k : Fin (Module.finrank ℚ_[p] (M i))),
      Real.log ‖y (Function.update d i k)‖ ≤ rho i) :
    ∀ (i : ι) (k : Fin (Module.finrank ℚ_[p] (M i))),
      Real.log ‖y (Function.update d i k)‖ ≤ rho i :=
  h

#check perPlaceDefaultRegion_target

end LeanFormal.IUT.XiFPaper.S2726DefaultIndexProbe
end
