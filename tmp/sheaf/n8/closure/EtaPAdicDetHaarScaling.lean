import tmp.sheaf.n8.closure.EtaGaussianActionVolumeFromDetActual
import LeanFormal.IUT.Foundations.LocalFields.PadicLatticeIndexFormula

/-!
# Eta p-adic determinant/Haar scaling: exact gap and conditional closure

The remaining measure-theoretic input for the Gaussian action-volume formula is

  mu (A '' S) = ||det A|| * mu S

for an additive Haar measure on the finite p-adic tensor block and a linear map
A with nonzero determinant.

Production has the Smith-normal-form lattice-index formula for Z_p-lattices
(PadicLatticeIndexFormula), and Mathlib has determinant/Haar scaling for real
vector spaces, but there is no theorem bridging a Q_p-linear determinant to the
index of an arbitrary lattice image.  This file records that exact missing
theorem and shows it would close the Gaussian volume formula.
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
open scoped TensorProduct

namespace LeanFormal.IUT.N8Closure.EtaPAdicDetHaarScaling

universe u

variable {p : Nat} [Fact p.Prime]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (A : ι → Type) [∀ i, NormedField (A i)]
  [∀ i, NormedAlgebra ℚ_[p] (A i)] [∀ i, FiniteDimensional ℚ_[p] (A i)]
variable (j : ι)

abbrev E : Type := (⨂[ℚ_[p]] (i : ι), A i)

variable [MeasurableSpace (E (p := p) A)] [BorelSpace (E (p := p) A)]

/-- Exact missing p-adic determinant/Haar scaling for linear maps on the finite
tensor block.  (A linear equivalence is a special case.) -/
def PAdicDetHaarScalingTheorem : Prop :=
  ∀ (μ : Measure (E (p := p) A)) (_hμ : μ.IsAddHaarMeasure)
    (f : E (p := p) A →ₗ[ℚ_[p]] E (p := p) A) (S : Set (E (p := p) A)),
    LinearMap.det f ≠ 0 → MeasurableSet S → 0 < μ S → μ S < ⊤ →
      (μ (f '' S)).toReal =
        ‖(LinearMap.det f : ℚ_[p])‖ * (μ S).toReal

/-- The exact Gaussian scaling statement follows from the missing determinant
scaling theorem and the actual determinant formula. -/
theorem actionHaarScaling_of_pAdicDetHaarScaling
    (h : PAdicDetHaarScalingTheorem (p := p) A)
    (μ : Measure (E (p := p) A)) [μ.IsAddHaarMeasure]
    (g : A j) (S : Set (E (p := p) A))
    (hnorm : Algebra.norm ℚ_[p] g ≠ 0)
    (hSmeas : MeasurableSet S) (hSpos : 0 < μ S) (hSfin : μ S < ⊤) :
    ActionHaarScaling (p := p) A j μ g S := by
  have hdet : LinearMap.det (gaussianAction (p := p) A j g) =
      (Algebra.norm ℚ_[p] g) ^
        (totalDim (p := p) A / factorDim (p := p) A j) := by
    exact tensorDetNormTarget_actual (p := p) A j g
  have hdet_ne : LinearMap.det (gaussianAction (p := p) A j g) ≠ 0 := by
    rw [hdet]
    exact pow_ne_zero _ hnorm
  have hscale := h μ inferInstance (gaussianAction (p := p) A j g) S hdet_ne
    hSmeas hSpos hSfin
  unfold ActionHaarScaling
  rw [hscale, hdet, norm_pow]

/-- Conditional closure of the Gaussian action-volume formula from the missing
p-adic determinant/Haar scaling theorem. -/
theorem gaussianActionVolume_of_pAdicDetHaarScaling
    (h : PAdicDetHaarScalingTheorem (p := p) A)
    (μ : Measure (E (p := p) A)) [μ.IsAddHaarMeasure]
    (g : A j) (S : Set (E (p := p) A))
    (hnorm : Algebra.norm ℚ_[p] g ≠ 0)
    (hSmeas : MeasurableSet S) (hSpos : 0 < μ S) (hSfin : μ S < ⊤) :
    normalizedLogVolume (p := p) A μ
        (gaussianAction (p := p) A j g '' S) -
      normalizedLogVolume (p := p) A μ S =
      Real.log ‖(Algebra.norm ℚ_[p] g : ℚ_[p])‖ /
        (factorDim (p := p) A j : Real) :=
  gaussianActionVolume_of_scaling (p := p) A j μ g S
    (actionHaarScaling_of_pAdicDetHaarScaling (p := p) A j h μ g S hnorm
      hSmeas hSpos hSfin)
    hSpos hSfin hnorm

end LeanFormal.IUT.N8Closure.EtaPAdicDetHaarScaling
