/- R1-I tensor lattice inclusion: positive fractional tensor lattice sits in the
valuation-integer tensor lattice.

Reuse (DONE trio):
* Mzk1URFracLatticeInclusionActual.padicFractionalLattice_subset_valuationInteger
* submoduleTensorSpan_mono (FinitePadicSubmoduleTensor)
-/
import tmp.sheaf.xif.paper.Mzk1URFracLatticeInclusionActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFractionalTensorLattice
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIntegerTensorComparison
import LeanFormal.IUT.ABCBridge.Geometry.FinitePadicSubmoduleTensor
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT.LocalFieldPadicTensor LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped LeanFormal.IUT.FinitePadicIntegralLattice Pointwise
namespace LeanFormal.IUT.XiFPaper.Mzk1G1R1ITensorLatticeDoneActual

open LeanFormal.IUT.NumberFieldFinitePlace

variable {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, Fintype (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)

local instance localInclusionTensorizationZpAlgebra :
    Algebra ℤ_[p] (ArithmeticTensorTupleBlock places tuple) :=
  Algebra.restrictScalars ℤ_[p] ℚ_[p] (ArithmeticTensorTupleBlock places tuple)

/-- Tensor version: if every coordinate exponent is positive, the fractional tensor
lattice is contained in the valuation-integer tensor lattice. -/
theorem arithmeticTupleFractionalLattice_le_valuationInteger
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    arithmeticTupleFractionalLattice places tuple a ≤
      arithmeticTupleValuationIntegerLattice places tuple := by
  unfold arithmeticTupleFractionalLattice arithmeticTupleValuationIntegerLattice
  apply submoduleTensorSpan_mono
  intro i
  exact Mzk1URFracLatticeInclusionActual.padicFractionalLattice_subset_valuationInteger
    (K := CommonPrimeCompletion (places i (tuple i))) (p := p) (a i) (ha i)

#print axioms arithmeticTupleFractionalLattice_le_valuationInteger
end LeanFormal.IUT.XiFPaper.Mzk1G1R1ITensorLatticeDoneActual
