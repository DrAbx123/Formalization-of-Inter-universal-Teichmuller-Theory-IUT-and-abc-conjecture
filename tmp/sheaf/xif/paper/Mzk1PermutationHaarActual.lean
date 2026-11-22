/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.MeasureTheory.Constructions.Pi
import LeanFormal.IUT.Foundations.LocalFields.PadicIntegerProductLattice

/-!
# Coordinate permutation invariance on the integral lattice (task-109)

Actual permutation action on `d → Q_p`; it preserves the coordinate lattice
and hence the product-Haar mass of the lattice.  This is the permutation
subgroup case of the missing `GL_d(Z_p)` Haar invariance; the full matrix
case remains a GAP. -/

noncomputable section
open scoped BigOperators
open MeasureTheory
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1PermutationHaarActual

open LeanFormal.IUT.PadicIntegerProductLattice

variable {p : Nat} [Fact p.Prime] {d : Type} [Fintype d] [DecidableEq d]
variable [MeasurableSpace ℚ_[p]]

/-- The integral coordinate lattice. -/
def coordLattice : Set (d → ℚ_[p]) :=
  {x | ∀ i, x i ∈ (1 : Submodule (PadicInt p) ℚ_[p])}

/-- Coordinate permutation action. -/
def permAct (σ : Equiv.Perm d) (x : d → ℚ_[p]) : d → ℚ_[p] :=
  fun i => x (σ i)

theorem permAct_symm_apply (σ : Equiv.Perm d) (x : d → ℚ_[p]) :
    permAct σ (permAct σ.symm x) = x := by
  funext i
  simp [permAct]

theorem permAct_image_coordLattice (σ : Equiv.Perm d) :
    permAct σ '' coordLattice (p := p) (d := d) = coordLattice (p := p) (d := d) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩ i
    exact hy (σ i)
  · intro hx
    refine ⟨permAct σ.symm x, ?_, permAct_symm_apply σ x⟩
    intro i
    exact hx (σ.symm i)

/-- Product-Haar mass of the coordinate lattice is invariant under coordinate
permutations.  The proof is set-level: the permutation maps the lattice onto
itself, so the measure of the image equals the measure of the lattice. -/
theorem measure_pi_perm_coordLattice (σ : Equiv.Perm d)
    (μ : Measure ℚ_[p]) [SigmaFinite μ] :
    (Measure.pi (fun _ : d => μ))
        (permAct σ '' coordLattice (p := p) (d := d)) =
      (Measure.pi (fun _ : d => μ)) (coordLattice (p := p) (d := d)) := by
  rw [permAct_image_coordLattice]

def permRows : List (String × String) :=
  [ ("permAct", "coordinate permutation action"),
    ("permAct_image_coordLattice", "lattice invariant"),
    ("measure_pi_perm_coordLattice", "product-Haar mass invariant"),
    ("full GL_d(Z_p) Haar invariance", "GAP") ]

theorem permRows_length : permRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1PermutationHaarActual
