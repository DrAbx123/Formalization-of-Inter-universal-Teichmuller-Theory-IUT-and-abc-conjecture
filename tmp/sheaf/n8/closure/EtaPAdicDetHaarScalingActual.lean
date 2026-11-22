import tmp.sheaf.n8.closure.EtaPAdicDetHaarScaling
import LeanFormal.IUT.Foundations.LocalFields.PadicLatticeIndexFormula
import Mathlib

/-!
# Eta p-adic determinant/Haar scaling actual: exact lattice-index gap

Production PadicLatticeIndexFormula computes the index of a full-rank
Z_p-sublattice from an explicit Smith normal form.  It does not prove the
missing bridge

  index(L / f L) = ||det_Qp f||^{-1}

for an arbitrary Q_p-linear f and lattice L, nor the resulting Haar scaling

  mu(f '' S) = ||det f|| * mu S.

This file records the exact missing bridge and closes the Gaussian volume
formula from it.  No arbitrary lattice, index, or factor is instantiated.
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
open scoped TensorProduct

namespace LeanFormal.IUT.N8Closure.EtaPAdicDetHaarScalingActual

universe u

variable {p : Nat} [Fact p.Prime]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (A : ι → Type) [∀ i, NormedField (A i)]
  [∀ i, NormedAlgebra ℚ_[p] (A i)] [∀ i, FiniteDimensional ℚ_[p] (A i)]
variable (j : ι)

abbrev E : Type := (⨂[ℚ_[p]] (i : ι), A i)

variable [MeasurableSpace (E (p := p) A)] [BorelSpace (E (p := p) A)]

/-- Exact missing lattice-index/determinant bridge, stated in the form needed
for the Haar scaling theorem. -/
def MissingPAdicLatticeIndexDetBridge : Prop :=
  ∀ (μ : Measure (E (p := p) A)) (_hμ : μ.IsAddHaarMeasure)
    (f : E (p := p) A →ₗ[ℚ_[p]] E (p := p) A) (S : Set (E (p := p) A)),
    LinearMap.det f ≠ 0 → MeasurableSet S → 0 < μ S → μ S < ⊤ →
      (μ (f '' S)).toReal =
        ‖(LinearMap.det f : ℚ_[p])‖ * (μ S).toReal

/-- The missing bridge is exactly the p-adic determinant/Haar scaling theorem. -/
theorem missingBridge_iff_pAdicDetHaarScaling :
    MissingPAdicLatticeIndexDetBridge (p := p) A ↔
      PAdicDetHaarScalingTheorem (p := p) A :=
  Iff.rfl

/-- Exact production fact that is available: the Smith-normal-form lattice
index formula itself (from PadicLatticeIndexFormula), not the determinant
bridge.  This records that the arithmetic index side exists. -/
theorem latticeIndex_pow_sum_available
    {M : Type*} [AddCommGroup M] [Module ℤ_[p] M]
    {κ : Type*} [Fintype κ]
    (N : Submodule ℤ_[p] M) (b : Module.Basis κ ℤ_[p] M)
    (h : Module.finrank ℤ_[p] N = Module.finrank ℤ_[p] M)
    (u : κ → ℤ_[p]ˣ) (k : κ → ℕ)
    (hunit : ∀ i,
      Submodule.smithNormalFormCoeffs b h i = (u i : ℤ_[p]) * (p : ℤ_[p]) ^ k i) :
    Nat.card (M ⧸ N) = p ^ ∑ i, k i :=
  LeanFormal.IUT.PadicLatticeIndex.natCard_quotient_eq_pow_sum_of_rankEq_unit_mul_pow
    N b h u k hunit

/-- Conditional closure of the Gaussian action-volume formula from the exact
missing lattice-index/determinant bridge. -/
theorem gaussianActionVolume_unconditional_of_latticeIndexDetBridge
    (h : MissingPAdicLatticeIndexDetBridge (p := p) A)
    (μ : Measure (E (p := p) A)) [μ.IsAddHaarMeasure]
    (g : A j) (S : Set (E (p := p) A))
    (hnorm : Algebra.norm ℚ_[p] g ≠ 0)
    (hSmeas : MeasurableSet S) (hSpos : 0 < μ S) (hSfin : μ S < ⊤) :
    normalizedLogVolume (p := p) A μ
        (gaussianAction (p := p) A j g '' S) -
      normalizedLogVolume (p := p) A μ S =
      Real.log ‖(Algebra.norm ℚ_[p] g : ℚ_[p])‖ /
        (factorDim (p := p) A j : Real) :=
  gaussianActionVolume_of_pAdicDetHaarScaling (p := p) A j
    ((missingBridge_iff_pAdicDetHaarScaling (p := p) A).mp h)
    μ g S hnorm hSmeas hSpos hSfin

end LeanFormal.IUT.N8Closure.EtaPAdicDetHaarScalingActual
