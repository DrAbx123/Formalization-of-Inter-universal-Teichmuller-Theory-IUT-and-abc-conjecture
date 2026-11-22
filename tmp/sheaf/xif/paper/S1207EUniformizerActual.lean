import tmp.sheaf.xif.paper.S1124EUnitFactorActual
import tmp.sheaf.xif.paper.S1116ERootStackDVRInstanceActual

noncomputable section
open scoped BigOperators Pointwise NNReal ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1207EUniformizerActual

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
open LeanFormal.IUT.XiFPaper.S1116ERootStackDVRInstanceActual
open LeanFormal.IUT.XiFPaper.S1124EUnitFactorActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Actual norm<1 for the S1116 DVR uniformizer. -/
theorem rootStackUniformizer_norm_lt_one :
    ‖((rootStackUniformizer (l := l) T b : Integers (rootStackExtension T b)) :
      rootStackExtension T b)‖ < 1 := by
  let π := rootStackUniformizer (l := l) T b
  have hle : ‖(π : rootStackExtension T b)‖ ≤ 1 :=
    (mem_integers_iff (K := rootStackExtension T b) (π : rootStackExtension T b)).mp π.property
  by_contra hnot
  have hge : 1 ≤ ‖(π : rootStackExtension T b)‖ := le_of_not_gt hnot
  have heq : ‖(π : rootStackExtension T b)‖ = 1 := le_antisymm hle hge
  let u : (Integers (rootStackExtension T b))ˣ :=
    unitOfNormOne (K := rootStackExtension T b) ⟨(π : rootStackExtension T b), heq⟩
  have hu : IsUnit π := by
    have h := u.isUnit
    simpa [u, unitOfNormOne] using h
  exact (rootStackUniformizer_irreducible (l := l) T b).not_isUnit hu

/-- The same uniformizer as a field unit. -/
noncomputable def rootStackUniformizerField :
    (rootStackExtension T b)ˣ :=
  Units.mk0 ((rootStackUniformizer (l := l) T b : Integers (rootStackExtension T b)) :
    rootStackExtension T b) (by
      intro h
      have hzero : rootStackUniformizer (l := l) T b = 0 := Subtype.ext h
      exact (rootStackUniformizer_irreducible (l := l) T b).ne_zero hzero)

/-- Exact DVR decomposition for the actual field uniformizer. -/
def S1207DVRDecomposition : Prop :=
  ∀ u : (rootStackExtension T b)ˣ,
    ∃ (n : Int) (eps : (rootStackExtension T b)ˣ),
      u = eps * rootStackUniformizerField (l := l) T b ^ n ∧
        ‖(eps : rootStackExtension T b)‖ = 1

/-- Exact uniformizer-factor formula. -/
def S1207UniformizerFactor : Prop :=
  rootStackHaarFactor (l := l) T b (rootStackUniformizerField (l := l) T b) =
    ENNReal.ofReal
      (‖(rootStackUniformizerField (l := l) T b :
        rootStackExtension T b)‖ ^ dQpFactor (l := l) T b)

/-- Exact factor-norm power formula. -/
def S1207FactorNormPow : Prop :=
  RootStackHaarFactorNormPow (l := l) T b (dQpFactor (l := l) T b)

/-- Remaining exact E data after the actual norm<1 and unit-factor results. -/
def S1207ExactRemainder : Prop :=
  S1207DVRDecomposition (l := l) T b ∧
    S1207UniformizerFactor (l := l) T b ∧
      S1207FactorNormPow (l := l) T b

/-- Exact remainder gives S885 uniformizer data, using S1124 actual unit factor. -/
noncomputable def s1207UniformizerData_of_remainder
    (h : S1207ExactRemainder (l := l) T b) :
    S885UniformizerData (l := l) T b where
  pi := rootStackUniformizerField (l := l) T b
  pi_norm_lt_one := rootStackUniformizer_norm_lt_one (l := l) T b
  unit_factor_one := s1124UnitFactorOne_actual (l := l) T b
  decomposition := h.1
  uniformizer_factor := h.2.1
  factor_norm_pow := h.2.2

end LeanFormal.IUT.XiFPaper.S1207EUniformizerActual

end
