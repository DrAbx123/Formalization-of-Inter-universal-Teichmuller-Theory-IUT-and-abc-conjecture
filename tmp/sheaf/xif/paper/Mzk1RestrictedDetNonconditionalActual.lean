/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HaarScalarOneActual
import tmp.sheaf.xif.paper.Mzk1DiagonalIndexActual

/-!
# Restricted determinant Haar identity (unimodular case, task-109)

Nonconditional in the **unimodular/image-equal** case: a continuous linear
equivalence preserving the coordinate lattice also preserves its Haar mass.
Together with the green diagonal quotient cardinal this is the restricted
det input; the general SNF/diagonal measure step remains GAP. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1RestrictedDetNonconditionalActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarScalarOneActual
open LeanFormal.IUT.XiFPaper.Mzk1DiagonalIndexActual
open LeanFormal.IUT.XiFPaper.Mzk1MatrixHaarBaseActual
variable {p : Nat} [Fact p.Prime] {d : Type} [Fintype d] [DecidableEq d]
variable [TopologicalSpace (d → ℚ_[p])] [MeasurableSpace (d → ℚ_[p])]
variable [IsTopologicalAddGroup (d → ℚ_[p])] [BorelSpace (d → ℚ_[p])]
variable [LocallyCompactSpace (d → ℚ_[p])]

/-- Unimodular restricted det step: if `L` preserves the coordinate lattice,
then it preserves its Haar mass (no conditional `hνO`). -/
theorem restricted_det_volume_of_image_eq
    (L : (d → ℚ_[p]) ≃L[ℚ_[p]] (d → ℚ_[p]))
    (h : L '' coordLattice (p := p) (d := d) = coordLattice (p := p) (d := d))
    (hO : IsOpen (coordLattice (p := p) (d := d)))
    (μ : Measure (d → ℚ_[p])) :
    (μ.map L) (coordLattice (p := p) (d := d)) =
      μ (coordLattice (p := p) (d := d)) :=
  map_coordLattice_eq_of_image_eq L h hO μ

/-- Re-export of the green diagonal quotient cardinal (restricted det index input). -/
theorem restricted_diag_index (e : d → Nat) :
    Nat.card ((d → PadicInt p) ⧸ diagLatticeSubmodule (p := p) e) = ∏ i, p ^ (e i) :=
  natCard_quotient_diagLatticeSubmodule (p := p) e
def restrictedDetNoncondRows : List (String × String) :=
  [ ("restricted_det_volume_of_image_eq", "unimodular/image-equal green"),
    ("restricted_diag_index", "diagonal quotient cardinal green"),
    ("general diagonal measure scaling", "GAP"),
    ("general SNF det formula", "GAP") ]
theorem restrictedDetNoncondRows_length : restrictedDetNoncondRows.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1RestrictedDetNonconditionalActual
