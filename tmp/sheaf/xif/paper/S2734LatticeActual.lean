import tmp.sheaf.xif.paper.S2734DecompUnitActual
import LeanFormal.IUT.Foundations.LocalFields.PadicIntegerProductLattice

noncomputable section
namespace LeanFormal.IUT.XiFPaper.S2734LatticeActual

open LeanFormal.IUT.PadicIntegerProductLattice
open LeanFormal.IUT.XiFPaper.S2734DecompUnitActual
open scoped Pointwise

variable {p : ℕ} [Fact p.Prime] {ι : Type*}

/-- Coercion ℤ_[p] → ℚ_[p] as a monoid hom. -/
def padicIntToPadic : ℤ_[p] →* ℚ_[p] where
  toFun z := (z : ℚ_[p])
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Integer units mapped to ℚ_[p]-units. -/
def unitQHom : (PadicInt p)ˣ →* ℚ_[p]ˣ :=
  Units.map padicIntToPadic

theorem unitQHom_coe (w : (PadicInt p)ˣ) :
    (unitQHom (p := p) w : ℚ_[p]) = (w : PadicInt p) := rfl

/-- The lattice is invariant under any integer unit. -/
theorem unitQ_smul_mem_lattice (w : (PadicInt p)ˣ)
    {x : ι → ℚ_[p]}
    (hx : x ∈ padicIntegerCoordinateLattice (p := p) (ι := ι)) :
    unitQHom (p := p) w • x ∈
      padicIntegerCoordinateLattice (p := p) (ι := ι) := by
  rcases hx with ⟨y, rfl⟩
  refine ⟨fun i => (w : PadicInt p) * y i, ?_⟩
  ext i
  simp [integerProductEmbedding, Pi.smul_apply, unitQHom, padicIntToPadic,
    Units.smul_def, smul_eq_mul]

/-- The lattice is equal to its image under an integer unit. -/
theorem unitQ_smul_lattice_eq (w : (PadicInt p)ˣ) :
    unitQHom (p := p) w •
      padicIntegerCoordinateLattice (p := p) (ι := ι) =
    padicIntegerCoordinateLattice (p := p) (ι := ι) := by
  apply le_antisymm
  · intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact unitQ_smul_mem_lattice w hy
  · intro x hx
    have hmem : unitQHom (p := p) w⁻¹ • x ∈
        padicIntegerCoordinateLattice (p := p) (ι := ι) :=
      unitQ_smul_mem_lattice (w⁻¹) hx
    have hx' : unitQHom (p := p) w •
        (unitQHom (p := p) w⁻¹ • x) = x := by
      rw [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
    rw [← hx']
    exact Set.smul_mem_smul_set hmem

#check unitQ_smul_lattice_eq
end LeanFormal.IUT.XiFPaper.S2734LatticeActual
end
