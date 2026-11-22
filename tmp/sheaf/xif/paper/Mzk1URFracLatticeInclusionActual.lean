import LeanFormal.IUT.Foundations.LocalFields.PadicFractionalLattice
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellLattice
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFractionalTensorLattice
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIntegerTensorComparison
import Mathlib.Tactic

/-!
# Fractional lattices sit inside the integral lattice (a > 0)

`padicFractionalLattice a` is the norm ball `{x | ‖x‖ ≤ p^{-a}}`.  For `a > 0` this is a
subset of the integer ball `Integers K` (the tensor/local integral lattice), hence
`arithmeticTupleFractionalLattice` is contained in the valuation-integer tensor lattice.
-/

noncomputable section
open LeanFormal.IUT.LocalFieldPadicTensor LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits

namespace LeanFormal.IUT.XiFPaper.Mzk1URFracLatticeInclusionActual

variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : ℕ} [Fact p.Prime] [NormedAlgebra ℚ_[p] K]

/-- For `a > 0` the fractional norm-ball lattice is contained in the integer lattice. -/
theorem padicFractionalLattice_subset_valuationInteger (a : ℝ) (ha : 0 < a) :
    padicFractionalLattice (p := p) (K := K) a ≤ valuationIntegerLattice (p := p) (K := K) := by
  intro x hx
  rw [mem_padicFractionalLattice_iff] at hx
  change x ∈ Integers K
  rw [mem_integers_iff]
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hmono : (p : ℝ) ^ (-a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith)
  linarith

#print axioms padicFractionalLattice_subset_valuationInteger
end LeanFormal.IUT.XiFPaper.Mzk1URFracLatticeInclusionActual