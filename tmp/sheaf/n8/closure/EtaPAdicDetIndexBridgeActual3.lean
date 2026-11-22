import tmp.sheaf.n8.closure.EtaPAdicSNFDetComparison
import tmp.sheaf.n8.closure.EtaPAdicDetHaarScalingActual
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Eta p-adic determinant/index bridge attempt 3

Available actual pieces:

* EtaPAdicSNFDetComparison: pure matrix determinant comparison
  det(U diag(a) V) = unit * prod a and ||det|| = ||prod a||.
* Mathlib Submodule.exists_smith_normal_form_of_le: Smith normal form for a
  submodule of a free module over a PID (here Z_p).

Missing for an arbitrary Q_p-linear f:

* a matrix Smith normal form A = U diag(a) V with U, V determinant units;
* the basis-change theorem identifying det_Qp(f) with det(A) and the lattice
  index [L : fL] with prod_i index(a_i);
* Haar uniqueness converting the lattice index to mu(f '' S) scaling.

This file records the exact missing bridge; no arbitrary matrix, lattice, or
factor is introduced.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option linter.overlappingInstances false
set_option linter.unusedVariables false
set_option linter.deprecated false

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.N8Closure.EtaTensorBlockDetActual
open LeanFormal.IUT.N8Closure.EtaTensorSplitActual
open LeanFormal.IUT.N8Closure.EtaGaussianActionVolumeFromDetActual
open LeanFormal.IUT.N8Closure.EtaPAdicDetHaarScaling
open LeanFormal.IUT.N8Closure.EtaPAdicDetHaarScalingActual
open LeanFormal.IUT.N8Closure.EtaPAdicSNFDetComparison
open scoped TensorProduct

namespace LeanFormal.IUT.N8Closure.EtaPAdicDetIndexBridgeActual3

universe u

variable {p : Nat} [Fact p.Prime]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (A : ι → Type) [∀ i, NormedField (A i)]
  [∀ i, NormedAlgebra ℚ_[p] (A i)] [∀ i, FiniteDimensional ℚ_[p] (A i)]
variable (j : ι)

abbrev E : Type := (⨂[ℚ_[p]] (i : ι), A i)

variable [MeasurableSpace (E (p := p) A)] [BorelSpace (E (p := p) A)]

/-- Exact missing matrix Smith normal form with unit determinant bases. -/
def MissingMatrixSNFUnitBases : Prop :=
  ∀ {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℤ_[p]),
    ∃ (U V : Matrix n n ℤ_[p]) (a : n → ℤ_[p]),
      M = U * Matrix.diagonal a * V ∧ IsUnit U.det ∧ IsUnit V.det

/-- Exact missing p-adic determinant/Haar scaling bridge. -/
def MissingPAdicDetHaarScalingBridge : Prop :=
  PAdicDetHaarScalingTheorem (p := p) A

/-- Conditional Gaussian action-volume closure from the missing p-adic bridge. -/
theorem gaussianActionVolume_of_pAdicDetIndexBridge3
    (h : MissingPAdicDetHaarScalingBridge (p := p) A)
    (μ : Measure (E (p := p) A)) [μ.IsAddHaarMeasure]
    (g : A j) (S : Set (E (p := p) A))
    (hnorm : Algebra.norm ℚ_[p] g ≠ 0)
    (hSmeas : MeasurableSet S) (hSpos : 0 < μ S) (hSfin : μ S < ⊤) :
    normalizedLogVolume (p := p) A μ
        (gaussianAction (p := p) A j g '' S) -
      normalizedLogVolume (p := p) A μ S =
      Real.log ‖(Algebra.norm ℚ_[p] g : ℚ_[p])‖ /
        (factorDim (p := p) A j : Real) :=
  gaussianActionVolume_of_pAdicDetHaarScaling (p := p) A j h
    μ g S hnorm hSmeas hSpos hSfin

/-- Exact gap: matrix SNF with unit bases plus determinant/lattice/Haar bridge. -/
structure EtaPAdicDetIndexBridgeGap where
  matrix_snf_unit_bases : MissingMatrixSNFUnitBases.{u} (p := p)
  p_adic_scaling : MissingPAdicDetHaarScalingBridge (p := p) A

end LeanFormal.IUT.N8Closure.EtaPAdicDetIndexBridgeActual3
