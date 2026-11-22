import tmp.sheaf.xif.paper.S827PaperValueGroupNormCardActual
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GeneralNormalizedNormConsumer
/-! # S829: spectral-uniqueness proof of the general normalized norm formula
The hard analytic step is actual: GeneralNormalizedNormBySpectralUniqueness /
Consumer prove ||x|| = absNorm^(-nu/d) by spectralNorm_unique_field_norm_ext.
What remains for the paper card is the arithmetic identification with
p^(-completionValuationExponent/e), plus the e alignment.  Both are recorded
exactly; the frozen card itself is not faked. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S829PaperNormValuationSpectralActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S827PaperValueGroupNormCardActual
open LeanFormal.IUT.GeneralNormalizedNormConsumer
open LeanFormal.IUT.IUTII.Frobenioid.Example36
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
/-- Actual general normalized norm formula at the paper place. -/
theorem paperGeneralNormalizedNormFormula
    (x : NormalizedCompletion (qVFamTensorPlace T b)) :
    ‖x‖ = (Ideal.absNorm (qVFamTensorPlace T b).maximalIdeal.asIdeal : ℝ) ^
      (-((nu (qVFamTensorPlace T b) x : ℝ) /
        ((relativeCompletionDegree (k := ℚ) (qVFamTensorPlace T b) : ℕ) : ℝ))) :=
  generalNormalizedNormFormula_consumer (qVFamTensorPlace T b) x
/-- Actual log form at the paper place. -/
theorem paperGeneralNormalizedLogFormula
    (x : NormalizedCompletion (qVFamTensorPlace T b)) :
    Real.log ‖x‖ =
      -(((nu (qVFamTensorPlace T b) x : ℝ) *
        Real.log (Ideal.absNorm (qVFamTensorPlace T b).maximalIdeal.asIdeal : ℝ)) /
        ((relativeCompletionDegree (k := ℚ) (qVFamTensorPlace T b) : ℕ) : ℝ)) :=
  generalNormalizedLogFormula_consumer (qVFamTensorPlace T b) x
/-- Exact arithmetic bridge still needed: identify the canonical absNorm
normalization with p^(-completionValuationExponent/e). -/
def PaperCanonicalToPadicBridge : Prop :=
  ∀ x : NormalizedCompletion (qVFamTensorPlace T b), x ≠ 0 →
    (Ideal.absNorm (qVFamTensorPlace T b).maximalIdeal.asIdeal : ℝ) ^
        (-(nu (qVFamTensorPlace T b) x : ℝ)) =
      (qVFamTensorP T b : ℝ) ^
        (-((completionValuationExponent (qVFamTensorPlace T b).maximalIdeal x : ℝ)))
/-- Actual spectral-uniqueness input plus exact arithmetic bridge. -/
def PaperNormValuationActualCore : Prop :=
  (∀ x : NormalizedCompletion (qVFamTensorPlace T b),
      ‖x‖ = (Ideal.absNorm (qVFamTensorPlace T b).maximalIdeal.asIdeal : ℝ) ^
        (-((nu (qVFamTensorPlace T b) x : ℝ) /
          ((relativeCompletionDegree (k := ℚ) (qVFamTensorPlace T b) : ℕ) : ℝ))))
  ∧ PaperCanonicalToPadicBridge (l := l) T b
end LeanFormal.IUT.XiFPaper.S829PaperNormValuationSpectralActual
