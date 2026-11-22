import tmp.sheaf.xif.paper.S2734LatticeActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

noncomputable section
open scoped NNReal
namespace LeanFormal.IUT.XiFPaper.S2736cTensorLatticeActual

open MeasureTheory
open LeanFormal.IUT.PadicIntegerProductLattice
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.S2734LatticeActual

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
variable (M : ι → Type*) [∀ i, NormedAddCommGroup (M i)]
variable [∀ i, NormedSpace ℚ_[p] (M i)]
variable [∀ i, FiniteDimensional ℚ_[p] (M i)]

/-- Tensor lattice: preimage of the coordinate integer lattice. -/
def tensorLattice : Set (FinitePadicTensor (p := p) M) :=
  (finitePadicTensorCoordinates (p := p) M) ⁻¹'
    padicIntegerCoordinateLattice (p := p) (ι := FinitePadicTensorIndex (p := p) M)

local instance tensorSetSMul :
    SMul ℚ_[p]ˣ (Set (FinitePadicTensor (p := p) M)) :=
  ⟨fun u S => (fun x => ((u : ℚ_[p]) • x)) '' S⟩

theorem tensorLattice_mem_iff (x : FinitePadicTensor (p := p) M) :
    x ∈ tensorLattice (p := p) M ↔
      finitePadicTensorCoordinates (p := p) M x ∈
        padicIntegerCoordinateLattice (p := p)
          (ι := FinitePadicTensorIndex (p := p) M) := Iff.rfl


theorem tensorLattice_unit_smul_eq (w : (PadicInt p)ˣ) :
    unitQHom (p := p) w • tensorLattice (p := p) M =
      tensorLattice (p := p) M := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [tensorLattice_mem_iff] at hy ⊢
    change finitePadicTensorCoordinates (p := p) M
      (((unitQHom (p := p) w : ℚ_[p]) • y)) ∈ _
    rw [map_smul]
    exact unitQ_smul_mem_lattice w hy
  · intro hx
    have hxL : finitePadicTensorCoordinates (p := p) M x ∈
        padicIntegerCoordinateLattice (p := p)
          (ι := FinitePadicTensorIndex (p := p) M) := by
      rwa [tensorLattice_mem_iff] at hx
    have hmem : unitQHom (p := p) w⁻¹ • x ∈ tensorLattice (p := p) M := by
      rw [tensorLattice_mem_iff]
      change finitePadicTensorCoordinates (p := p) M
        (((unitQHom (p := p) w⁻¹ : ℚ_[p]) • x)) ∈ _
      rw [map_smul]
      exact unitQ_smul_mem_lattice (w⁻¹) hxL
    refine ⟨unitQHom (p := p) w⁻¹ • x, hmem, ?_⟩
    change ((unitQHom (p := p) w : ℚ_[p]) •
      ((unitQHom (p := p) w⁻¹ : ℚ_[p]) • x)) = x
    rw [smul_smul]
    rw [show unitQHom (p := p) w⁻¹ = (unitQHom (p := p) w)⁻¹ from map_inv _ _]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]


#check tensorLattice_unit_smul_eq
#check tensorLattice_unit_smul_eq

#check tensorLattice
#check tensorLattice_mem_iff
end LeanFormal.IUT.XiFPaper.S2736cTensorLatticeActual
end
