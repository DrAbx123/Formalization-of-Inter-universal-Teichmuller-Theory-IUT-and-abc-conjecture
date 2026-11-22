/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1CanonicalHaarInvarianceActual
import LeanFormal.IUT.Foundations.LocalFields.PadicIntegerProductLattice

/-! # Canonical Haar coordinate-compact and full lattice invariance (task-109) -/
noncomputable section
open scoped BigOperators
open MeasureTheory
open MeasureTheory.Measure
namespace LeanFormal.IUT.XiFPaper.Mzk1CanonicalHaarCoordLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1CanonicalHaarInvarianceActual
open LeanFormal.IUT.XiFPaper.Mzk1MatrixHaarBaseActual
open LeanFormal.IUT.PadicIntegerProductLattice
variable {p : Nat} [Fact p.Prime] {d : Type} [Fintype d] [DecidableEq d]
variable [MeasurableSpace (d → ℚ_[p])] [BorelSpace (d → ℚ_[p])]

theorem coordLattice_eq_padicIntegerCoordinateLattice :
    coordLattice (p := p) (d := d) =
      padicIntegerCoordinateLattice (p := p) (ι := d) := by
  ext x
  constructor
  · intro hx
    choose y hy using fun i => (Submodule.mem_one.mp (hx i))
    refine ⟨y, ?_⟩
    funext i
    simpa [integerProductEmbedding] using (hy i)
  · rintro ⟨y, rfl⟩ i
    exact Submodule.mem_one.mpr ⟨y i, rfl⟩

/-- The coordinate lattice as a positive compact, under the canonical Pi topology. -/
noncomputable def coordinateCompacts : TopologicalSpace.PositiveCompacts (d → ℚ_[p]) where
  carrier := coordLattice (p := p) (d := d)
  isCompact' := by
    rw [coordLattice_eq_padicIntegerCoordinateLattice]
    exact isCompact_padicIntegerCoordinateLattice
  interior_nonempty' := by
    have hopen : IsOpen (coordLattice (p := p) (d := d) : Set (d → ℚ_[p])) := by
      rw [coordLattice_eq_padicIntegerCoordinateLattice]
      exact isOpen_padicIntegerCoordinateLattice
    rw [hopen.interior_eq]
    exact ⟨0, by simp [coordLattice]⟩

theorem coordinateCompacts_mass :
    addHaarMeasure (coordinateCompacts (p := p) (d := d))
        (coordLattice (p := p) (d := d)) = 1 := by
  simpa [coordinateCompacts] using (addHaarMeasure_self (K₀ := coordinateCompacts (p := p) (d := d)))

theorem canonical_map_eq_of_image_eq_full
    (L : (d → ℚ_[p]) ≃L[ℚ_[p]] (d → ℚ_[p]))
    (h : L '' coordLattice (p := p) (d := d) =
      coordLattice (p := p) (d := d)) :
    (addHaarMeasure (coordinateCompacts (p := p) (d := d))).map L =
      addHaarMeasure (coordinateCompacts (p := p) (d := d)) := by
  have hmass : addHaarMeasure (coordinateCompacts (p := p) (d := d))
      (coordLattice (p := p) (d := d)) = 1 := by
    simpa [coordinateCompacts] using (addHaarMeasure_self (K₀ := coordinateCompacts (p := p) (d := d)))
  have hpos : addHaarMeasure (coordinateCompacts (p := p) (d := d))
      (coordLattice (p := p) (d := d)) ≠ 0 :=
    by rw [hmass]; exact one_ne_zero
  have hfin : addHaarMeasure (coordinateCompacts (p := p) (d := d))
      (coordLattice (p := p) (d := d)) ≠ ⊤ :=
    by rw [hmass]; exact ENNReal.one_ne_top
  have hopen : IsOpen (coordLattice (p := p) (d := d) : Set (d → ℚ_[p])) := by
    rw [coordLattice_eq_padicIntegerCoordinateLattice]
    exact isOpen_padicIntegerCoordinateLattice
  exact canonical_map_eq_of_image_eq (coordinateCompacts (p := p) (d := d)) L h hopen hpos hfin
def canonicalCoordRows : List (String × String) :=
  [ ("coordinateCompacts", "green Pi topology"),
    ("coordinateCompacts_mass", "green =1"),
    ("canonical_map_eq_of_image_eq_full", "unconditional canonical") ]
theorem canonicalCoordRows_length : canonicalCoordRows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1CanonicalHaarCoordLatticeActual
