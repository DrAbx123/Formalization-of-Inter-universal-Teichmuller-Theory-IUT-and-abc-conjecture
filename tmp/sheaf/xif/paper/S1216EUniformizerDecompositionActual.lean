import tmp.sheaf.xif.paper.S1207EUniformizerActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits

noncomputable section
open scoped BigOperators Pointwise NNReal ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1216EUniformizerDecompositionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S1116ERootStackDVRInstanceActual
open LeanFormal.IUT.XiFPaper.S1207EUniformizerActual
open LeanFormal.IUT.XiFPaper.S885RootStackUniformizerNormActual
open LeanFormal.IUT.XiFPaper.S878RootStackCharacterNormDirectActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Actual DVR decomposition for E-units: u = eps * pi^n, with eps norm one. -/
theorem s1216DVRDecomposition_actual :
    S1207DVRDecomposition T b := by
  intro u
  have hx : ((u : (rootStackExtension T b)ˣ) :
      rootStackExtension T b) ≠ 0 := Units.ne_zero u
  obtain ⟨n, v, hv⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
      (R := Integers (rootStackExtension T b))
      (K := rootStackExtension T b)
      (hϖ := rootStackUniformizer_irreducible T b) hx
  let eps : (rootStackExtension T b)ˣ :=
    Units.map (algebraMap (Integers (rootStackExtension T b))
      (rootStackExtension T b)).toMonoidHom v
  refine ⟨n, eps, ?_, ?_⟩
  · apply Units.ext
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val]
    rw [hv]
    rw [Units.smul_def]
    rfl
  · change ‖((v : Integers (rootStackExtension T b)) :
      rootStackExtension T b)‖ = 1
    exact norm_unit_eq_one v

/-- S885 data from the actual DVR decomposition and the two remaining exact
factor inputs. -/
noncomputable def s1216UniformizerData_of_factor
    (hfactor : S1207UniformizerFactor T b)
    (hpow : S1207FactorNormPow T b) :
    S885UniformizerData T b :=
  s1207UniformizerData_of_remainder (T := T) b
    ⟨s1216DVRDecomposition_actual T b, hfactor, hpow⟩

/-- Exact first unresolved item for the E uniformizer factor. -/
def S1216UniformizerFactorGap : Prop :=
  S1207UniformizerFactor T b

/-- Exact second item: general factor-norm power formula. -/
def S1216FactorNormPowGap : Prop :=
  S1207FactorNormPow T b

end LeanFormal.IUT.XiFPaper.S1216EUniformizerDecompositionActual

end
