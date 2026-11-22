import tmp.sheaf.xif.paper.S2734LatticeActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.S2735CharVActual

open MeasureTheory
open LeanFormal.IUT.PadicIntegerProductLattice
open LeanFormal.IUT.XiFPaper.S2734LatticeActual

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Finite ι]

/-- Integer units act with Haar character one on coordinate space. -/
theorem unitQ_char_eq_one (w : (PadicInt p)ˣ) :
    distribHaarChar (ι → ℚ_[p]) (unitQHom (p := p) w) = 1 := by
  letI : MeasurableSpace (ι → ℚ_[p]) := borel _
  letI : BorelSpace (ι → ℚ_[p]) := ⟨rfl⟩
  let μ : Measure (ι → ℚ_[p]) := Measure.addHaar
  let L := padicIntegerCoordinateLattice (p := p) (ι := ι)
  have hpos : 0 < μ L := by
    have hopen := isOpen_padicIntegerCoordinateLattice (p := p) (ι := ι)
    exact hopen.measure_pos μ ⟨0, zero_mem_padicIntegerCoordinateLattice⟩
  have hfin : μ L < ⊤ :=
    isCompact_padicIntegerCoordinateLattice.measure_lt_top
  apply distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ)
    hpos.ne' hfin.ne (r := 1)
  rw [show L = padicIntegerCoordinateLattice (p := p) (ι := ι) from rfl]
  rw [unitQ_smul_lattice_eq]
  simp

#check unitQ_char_eq_one
end LeanFormal.IUT.XiFPaper.S2735CharVActual
end
