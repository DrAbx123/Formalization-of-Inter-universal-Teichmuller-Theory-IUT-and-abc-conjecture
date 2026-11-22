import tmp.sheaf.xif.paper.S1207EUniformizerActual
import tmp.sheaf.xif.paper.S887RootStackHaarDetViaS861EActual

noncomputable section
open scoped BigOperators Pointwise NNReal ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1308EUniformizerFactorFromCharacterActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S831StackHaarDimensionActual
open LeanFormal.IUT.XiFPaper.S878RootStackCharacterNormDirectActual
open LeanFormal.IUT.XiFPaper.S885RootStackUniformizerNormActual
open LeanFormal.IUT.XiFPaper.S887RootStackHaarDetViaS861EActual
open LeanFormal.IUT.XiFPaper.S1207EUniformizerActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- The exact E character/norm comparison implies the uniformizer factor. -/
theorem s1308UniformizerFactor_of_ECharacter
    (h : RootStackCharacterNormComparisonAtDQp (l := l) T b) :
    S1207UniformizerFactor (l := l) T b := by
  unfold S1207UniformizerFactor
  let lam : (rootStackExtension T b)ˣ := rootStackUniformizerField (l := l) T b
  have hne : rootStackHaarFactor T b lam ≠ ⊤ := by
    unfold rootStackHaarFactor
    exact ENNReal.coe_ne_top
  rw [← ENNReal.toReal_eq_toReal_iff' hne (by simp)]
  have hto : (rootStackHaarFactor T b lam).toReal =
      (MeasureTheory.distribHaarChar (rootStackExtension T b) lam : Real) := by
    unfold rootStackHaarFactor
    rw [ENNReal.coe_toReal]
  rw [hto, ENNReal.toReal_ofReal (by positivity)]
  apply Real.log_injOn_pos
  · exact_mod_cast (MeasureTheory.distribHaarChar_pos
      (A := rootStackExtension T b) (g := lam))
  · exact pow_pos (norm_pos_iff.mpr (Units.ne_zero lam)) _
  rw [Real.log_pow]
  exact h lam

/-- Exact first analytic input: the E character/norm comparison. -/
def S1308ExactFirstAnalytic : Prop :=
  RootStackCharacterNormComparisonAtDQp (l := l) T b

end LeanFormal.IUT.XiFPaper.S1308EUniformizerFactorFromCharacterActual

end
