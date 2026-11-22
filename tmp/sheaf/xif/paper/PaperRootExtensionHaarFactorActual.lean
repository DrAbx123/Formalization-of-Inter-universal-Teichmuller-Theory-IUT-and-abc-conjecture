import tmp.sheaf.xif.paper.PaperRootExtensionPrimeScalingActual
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

/-! # Multiplicativity and unit triviality of the root Haar scaling factor -/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

noncomputable section
open scoped BigOperators Pointwise NNReal ENNReal

namespace LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarFactorActual

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionValuedActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionDiscreteValuationActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionPrimeDecompositionActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionPrimeScalingActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Actual Haar scaling factor of a field unit, as the distribution character. -/
noncomputable def rootHaarFactor (lam : (rootNormedExtension T b)ˣ) : ENNReal :=
  (distribHaarChar (rootNormedExtension T b) lam : ENNReal)

/-- Factor is multiplicative. -/
theorem rootHaarFactor_mul (lam μ : (rootNormedExtension T b)ˣ) :
    rootHaarFactor T b (lam * μ) =
      rootHaarFactor T b lam * rootHaarFactor T b μ := by
  unfold rootHaarFactor
  rw [map_mul, ENNReal.coe_mul]

/-- Unit-norm scaling has factor one. -/
theorem rootHaarFactor_eq_one_of_norm_one
    (lam : (rootNormedExtension T b)ˣ)
    (h : ‖(lam : rootNormedExtension T b)‖ = 1) :
    rootHaarFactor T b lam = 1 := by
  have hO : (lam : rootNormedExtension T b) • rootExtensionUnitBall T b =
      rootExtensionUnitBall T b := by
    unfold rootExtensionUnitBall
    rw [smul_unitClosedBall, h]
  have hpos : rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ 0 :=
    ne_of_gt (rootExtensionUnitBall_measure_pos T b)
  have hfin : rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ ⊤ :=
    ne_of_lt (rootExtensionUnitBall_measure_lt_top T b)
  have hchar : distribHaarChar (rootNormedExtension T b) lam = 1 := by
    apply distribHaarChar_eq_of_measure_smul_eq_mul
      (μ := rootExtensionHaar T b) (g := lam) (s := rootExtensionUnitBall T b)
      (r := 1) hpos hfin
    have hO' : lam • rootExtensionUnitBall T b = rootExtensionUnitBall T b := by
      simpa only [Units.smul_def] using hO
    rw [hO']
    simp
  unfold rootHaarFactor
  rw [hchar]
  simp


/-- The factor is the actual measure ratio on the unit ball. -/
theorem rootHaarFactor_eq_ratio (lam : (rootNormedExtension T b)ˣ) :
    rootHaarFactor T b lam =
      rootExtensionHaar T b (lam • rootExtensionUnitBall T b) /
        rootExtensionHaar T b (rootExtensionUnitBall T b) := by
  unfold rootHaarFactor
  rw [distribHaarChar_eq_div
    (μ := rootExtensionHaar T b)
    (s := rootExtensionUnitBall T b)
    (ne_of_gt (rootExtensionUnitBall_measure_pos T b))
    (ne_of_lt (rootExtensionUnitBall_measure_lt_top T b))]

/-- The rational prime as a field unit. -/
noncomputable def rootPrimeFieldUnit : (rootNormedExtension T b)ˣ :=
  Units.mk0 (algebraMap ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)
    (qVFamTensorP T b) : rootNormedExtension T b) (by
      intro h
      exact (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime (qVFamTensorP T b)).ne_zero)
        ((algebraMap ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)).injective
          (by simpa using h)))


/-- The actual Haar factor of the rational prime is the d-th power of its norm. -/
theorem rootHaarFactor_prime_eq_norm_pow :
    rootHaarFactor T b (rootPrimeFieldUnit T b) =
      ENNReal.ofReal (‖(algebraMap ℚ_[(qVFamTensorP T b)]
        (rootNormedExtension T b) (qVFamTensorP T b) :
          rootNormedExtension T b)‖ ^
        Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)) := by
  rw [rootHaarFactor_eq_ratio]
  change rootExtensionHaar T b
      ((algebraMap ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)
        (qVFamTensorP T b) : rootNormedExtension T b) •
        rootExtensionUnitBall T b) /
      rootExtensionHaar T b (rootExtensionUnitBall T b) = _
  have hset : ((algebraMap ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)
        (qVFamTensorP T b) : rootNormedExtension T b) •
        rootExtensionUnitBall T b) =
      ((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) •
        rootExtensionUnitBall T b) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, by simp [Algebra.smul_def, smul_eq_mul]⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, by simp [Algebra.smul_def, smul_eq_mul]⟩
  rw [hset, rootPrime_smul_measure]
  exact ENNReal.mul_div_cancel_right
    (ne_of_gt (rootExtensionUnitBall_measure_pos T b))
    (ne_of_lt (rootExtensionUnitBall_measure_lt_top T b))

/-- Factor of a power. -/
theorem rootHaarFactor_pow (lam : (rootNormedExtension T b)ˣ) (n : Nat) :
    rootHaarFactor T b (lam ^ n) = rootHaarFactor T b lam ^ n := by
  unfold rootHaarFactor
  rw [map_pow, ENNReal.coe_pow]

end LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarFactorActual

end