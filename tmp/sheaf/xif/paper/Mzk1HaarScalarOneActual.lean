/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1MatrixHaarBaseActual
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Regular

/-! # c=1 normalization for Haar scalar factor (task-109, conditional step) -/
noncomputable section
open scoped BigOperators
open MeasureTheory
open MeasureTheory.Measure
namespace LeanFormal.IUT.XiFPaper.Mzk1HaarScalarOneActual
open LeanFormal.IUT.XiFPaper.Mzk1MatrixHaarBaseActual
variable {p : Nat} [Fact p.Prime] {d : Type} [Fintype d] [DecidableEq d]
variable [TopologicalSpace (d → ℚ_[p])] [MeasurableSpace (d → ℚ_[p])]
variable [IsTopologicalAddGroup (d → ℚ_[p])] [BorelSpace (d → ℚ_[p])]
variable [LocallyCompactSpace (d → ℚ_[p])]

/-- If `L` preserves the mass of the open coordinate lattice, then its Haar
scalar factor is `1`.  The equality `hνO` is exactly the lattice mass
equality; the remaining GAP is to derive it from `L '' coordLattice = coordLattice`.
-/
theorem addHaarScalarFactor_eq_one_of_lattice
    (L : (d → ℚ_[p]) ≃L[ℚ_[p]] (d → ℚ_[p]))
    (μ : Measure (d → ℚ_[p])) [Measure.IsAddHaarMeasure μ]
    (hO : IsOpen (coordLattice (p := p) (d := d)))
    (hOpos : μ (coordLattice (p := p) (d := d)) ≠ 0)
    (hOfin : μ (coordLattice (p := p) (d := d)) ≠ ⊤)
    (hνO : (μ.map L) (coordLattice (p := p) (d := d)) =
      μ (coordLattice (p := p) (d := d))) :
    addHaarScalarFactor (μ.map L) μ = 1 := by
  haveI : Measure.IsAddHaarMeasure (μ.map L) :=
    ContinuousLinearEquiv.isAddHaarMeasure_map L μ
  have h := measure_isAddHaarMeasure_eq_smul_of_isOpen (μ.map L) μ hO
  rw [hνO] at h
  have hc : ((addHaarScalarFactor (μ.map L) μ : ℝ) *
      (μ (coordLattice (p := p) (d := d))).toReal) =
      (μ (coordLattice (p := p) (d := d))).toReal := by
    have := congrArg ENNReal.toReal h.symm
    simpa [ENNReal.toReal_smul, smul_eq_mul] using this
  have hx0 : (μ (coordLattice (p := p) (d := d))).toReal ≠ 0 :=
    (ENNReal.toReal_pos hOpos hOfin).ne'
  have hc1 : (addHaarScalarFactor (μ.map L) μ : ℝ) = 1 :=
    mul_right_cancel₀ hx0 (by simpa using hc)
  exact_mod_cast hc1

/-- If `L` maps the open coordinate lattice onto itself, then `L` preserves
the mass of that lattice.  This is the `hνO` input of the c=1 theorem. -/
theorem map_coordLattice_eq_of_image_eq
    (L : (d → ℚ_[p]) ≃L[ℚ_[p]] (d → ℚ_[p]))
    (h : L '' coordLattice (p := p) (d := d) = coordLattice (p := p) (d := d))
    (hO : IsOpen (coordLattice (p := p) (d := d)))
    (μ : Measure (d → ℚ_[p])) :
    (μ.map L) (coordLattice (p := p) (d := d)) =
      μ (coordLattice (p := p) (d := d)) := by
  rw [Measure.map_apply L.continuous.measurable hO.measurableSet]
  congr 1
  ext x
  constructor
  · intro hx
    have hLx : L x ∈ coordLattice (p := p) (d := d) := hx
    have hLxImage : L x ∈ L '' coordLattice (p := p) (d := d) := by
      rw [h]
      exact hLx
    rcases hLxImage with ⟨y, hy, hyx⟩
    have : y = x := L.injective hyx
    simpa [this] using hy
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩

/-- c=1 normalization from the actual image equality (no separate hνO). -/
theorem addHaarScalarFactor_eq_one_of_image
    (L : (d → ℚ_[p]) ≃L[ℚ_[p]] (d → ℚ_[p]))
    (h : L '' coordLattice (p := p) (d := d) = coordLattice (p := p) (d := d))
    (hO : IsOpen (coordLattice (p := p) (d := d)))
    (μ : Measure (d → ℚ_[p])) [Measure.IsAddHaarMeasure μ]
    (hOpos : μ (coordLattice (p := p) (d := d)) ≠ 0)
    (hOfin : μ (coordLattice (p := p) (d := d)) ≠ ⊤) :
    (μ.map L).addHaarScalarFactor μ = 1 :=
  addHaarScalarFactor_eq_one_of_lattice L μ hO hOpos hOfin
    (map_coordLattice_eq_of_image_eq L h hO μ)


/-- Full measurable-set version, conditional only on outer regularity of the
two Haar measures: equality on all open sets plus `OuterRegular.ext_isOpen`. -/
theorem map_eq_of_image_eq
    (L : (d → ℚ_[p]) ≃L[ℚ_[p]] (d → ℚ_[p]))
    (h : L '' coordLattice (p := p) (d := d) = coordLattice (p := p) (d := d))
    (hO : IsOpen (coordLattice (p := p) (d := d)))
    (μ : Measure (d → ℚ_[p])) [Measure.IsAddHaarMeasure μ]
    [Measure.OuterRegular μ] [Measure.OuterRegular (μ.map L)]
    (hOpos : μ (coordLattice (p := p) (d := d)) ≠ 0)
    (hOfin : μ (coordLattice (p := p) (d := d)) ≠ ⊤) :
    μ.map L = μ := by
  haveI : Measure.IsAddHaarMeasure (μ.map L) :=
    ContinuousLinearEquiv.isAddHaarMeasure_map L μ
  have hc := addHaarScalarFactor_eq_one_of_image L h hO μ hOpos hOfin
  apply Measure.OuterRegular.ext_isOpen
  intro U hU
  have hu := measure_isAddHaarMeasure_eq_smul_of_isOpen (μ.map L) μ hU
  rwa [hc, one_smul] at hu

def scalarOneRows : List (String × String) :=
  [ ("addHaarScalarFactor_eq_one_of_lattice", "conditional c=1"),
    ("derive hνO from lattice image", "GAP") ]
theorem scalarOneRows_length : scalarOneRows.length = 2 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1HaarScalarOneActual
