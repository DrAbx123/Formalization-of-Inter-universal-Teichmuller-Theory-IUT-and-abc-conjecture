import tmp.sheaf.n8.closure.EtaTensorSplitActual
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Eta Gaussian action volume from determinant: conditional actual

EtaTensorSplitActual proves the actual determinant formula

  det(tensor pure action) = Norm(g) ^ (D / d_j).

The missing measure-theoretic step is the additive-Haar determinant scaling on
the p-adic tensor block:

  mu (A '' S) = ||det A|| * mu S.

Mathlib supplies determinant/Haar scaling for real vector spaces, but not for
the p-adic finite tensor block.  Under the exact scaling statement this file
proves the normalized Gaussian action-volume formula

  nu(A S) - nu(S) = log ||Norm(g)|| / d_j,

where nu = log(mu)/D and D = prod_i d_i.  No arbitrary measure, region, or
volume is instantiated.
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
open scoped TensorProduct

namespace LeanFormal.IUT.N8Closure.EtaGaussianActionVolumeFromDetActual

universe u

variable {p : Nat} [Fact p.Prime]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (A : ι → Type) [∀ i, NormedField (A i)]
  [∀ i, NormedAlgebra ℚ_[p] (A i)] [∀ i, FiniteDimensional ℚ_[p] (A i)]
variable (j : ι)

/-- The actual tensor block carrier. -/
abbrev E : Type := (⨂[ℚ_[p]] (i : ι), A i)

variable [MeasurableSpace (E (p := p) A)] [BorelSpace (E (p := p) A)]

/-- Actual pure-tensor action. -/
def gaussianAction (g : A j) : E (p := p) A →ₗ[ℚ_[p]] E (p := p) A :=
  tensorActionMul (p := p) A j g

/-- Normalized log-volume, normalized by D = prod_i [A_i : Q_p]. -/
def normalizedLogVolume (μ : Measure (E (p := p) A)) (S : Set (E (p := p) A)) : Real :=
  Real.log (μ S).toReal / (totalDim (p := p) A : Real)

/-- Exact missing additive-Haar determinant scaling for the p-adic tensor block. -/
def ActionHaarScaling (μ : Measure (E (p := p) A)) (g : A j)
    (S : Set (E (p := p) A)) : Prop :=
  (μ (gaussianAction (p := p) A j g '' S)).toReal =
    ‖(Algebra.norm ℚ_[p] g : ℚ_[p])‖ ^
      (totalDim (p := p) A / factorDim (p := p) A j) * (μ S).toReal

theorem totalDim_pos : 0 < totalDim (p := p) A := by
  unfold totalDim factorDim
  exact Finset.prod_pos (fun i _ => Module.finrank_pos (R := ℚ_[p]) (M := A i))

theorem totalDim_ne_zero : totalDim (p := p) A ≠ 0 :=
  (totalDim_pos (p := p) A).ne'

theorem factorDim_pos (j : ι) : 0 < factorDim (p := p) A j := by
  unfold factorDim
  exact Module.finrank_pos (R := ℚ_[p]) (M := A j)


theorem factorDim_dvd_totalDim (j : ι) : factorDim (p := p) A j ∣ totalDim (p := p) A := by
  unfold totalDim factorDim
  rw [Finset.prod_eq_mul_prod_diff_singleton j]
  · exact dvd_mul_right _ _
  · intro hj
    simp at hj

/-- Conditional actual Gaussian action-volume formula from the missing Haar
determinant scaling. -/
theorem gaussianActionVolume_of_scaling (μ : Measure (E (p := p) A))
    [μ.IsAddHaarMeasure] (g : A j) (S : Set (E (p := p) A))
    (hscale : ActionHaarScaling (p := p) A j μ g S)
    (hSpos : 0 < μ S) (hSfin : μ S < ⊤)
    (hnorm : Algebra.norm ℚ_[p] g ≠ 0) :
    normalizedLogVolume (p := p) A μ
        (gaussianAction (p := p) A j g '' S) -
      normalizedLogVolume (p := p) A μ S =
      Real.log ‖(Algebra.norm ℚ_[p] g : ℚ_[p])‖ /
        (factorDim (p := p) A j : Real) := by
  have hS : 0 < (μ S).toReal := ENNReal.toReal_pos hSpos.ne' hSfin.ne
  have hnorm_pos : 0 < ‖(Algebra.norm ℚ_[p] g : ℚ_[p])‖ := norm_pos_iff.mpr hnorm
  let D : Real := (totalDim (p := p) A : Real)
  let d : Real := (factorDim (p := p) A j : Real)
  have hD : D ≠ 0 := by
    unfold D
    exact_mod_cast totalDim_ne_zero (p := p) A
  have hd : d ≠ 0 := by
    unfold d
    exact_mod_cast (factorDim_pos (p := p) A j).ne'
  have hlog :
      Real.log (μ (gaussianAction (p := p) A j g '' S)).toReal =
        (totalDim (p := p) A / factorDim (p := p) A j : Real) *
            Real.log ‖(Algebra.norm ℚ_[p] g : ℚ_[p])‖ + Real.log (μ S).toReal := by
    rw [hscale]
    rw [Real.log_mul (pow_ne_zero _ hnorm_pos.ne') hS.ne',
      Real.log_pow]
    rw [Nat.cast_div_charZero (factorDim_dvd_totalDim (p := p) A j)]
  unfold normalizedLogVolume
  rw [hlog]
  field_simp [D, d, hD, hd]
  ring

/-- Exact universally quantified missing production theorem: determinant/Haar
scaling for additive Haar on the p-adic finite tensor block. -/
def MissingDeterminantHaarScalingTheorem : Prop :=
  ∀ (μ : Measure (E (p := p) A)) (_hμ : μ.IsAddHaarMeasure) (g : A j)
    (S : Set (E (p := p) A)), MeasurableSet S → 0 < μ S → μ S < ⊤ →
      ActionHaarScaling (p := p) A j μ g S

/-- Exact gap of the Gaussian action-volume route. -/
structure GaussianActionVolumeGap (g : A j) where
  μ : Measure (E (p := p) A)
  addHaar : μ.IsAddHaarMeasure
  S : Set (E (p := p) A)
  measurable_S : MeasurableSet S
  pos_S : 0 < μ S
  finite_S : μ S < ⊤
  scaling : ActionHaarScaling (p := p) A j μ g S

end LeanFormal.IUT.N8Closure.EtaGaussianActionVolumeFromDetActual
