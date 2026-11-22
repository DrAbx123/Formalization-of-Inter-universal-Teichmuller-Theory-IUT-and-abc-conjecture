import tmp.sheaf.xif.paper.S824RootStackyHaarVolumeActual
import tmp.sheaf.xif.paper.S831StackHaarDimensionActual
import tmp.sheaf.xif.paper.S782FiniteRootStackExtensionActual
/-! # S878: direct E=rootStackExtension character/norm comparison
The L-layer comparison is actual (S865).  For E the tree has the carrier and
degree dStack, but no proven DVR uniformizer/norm formula on E.  This file
reduces the E comparison to the exact factor-norm formula and records the
uniformizer data; no no-go. -/
noncomputable section
open scoped BigOperators Pointwise NNReal ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S878RootStackCharacterNormDirectActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S831StackHaarDimensionActual
open LeanFormal.IUT.XiFPaper.S824RootStackyHaarVolumeActual
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
/-- Haar factor on E. -/
noncomputable def rootStackHaarFactor (u : (rootStackExtension T b)ˣ) : ENNReal :=
  (distribHaarChar (rootStackExtension T b) u : ENNReal)
/-- Exact E factor-norm formula. -/
def RootStackHaarFactorNormPow (n : Nat) : Prop :=
  ∀ u : (rootStackExtension T b)ˣ,
    rootStackHaarFactor T b u = ENNReal.ofReal
      ((‖(u : rootStackExtension T b)‖) ^ n)
/-- The E character/norm comparison follows from the factor formula. -/
theorem stackCharacterNormComparison_of_factorNormPow
    (n : Nat) (h : RootStackHaarFactorNormPow (l := l) T b n) :
    StackCharacterNormComparison (l := l) T b n := by
  intro u
  have hfac := h u
  have hto : (rootStackHaarFactor T b u).toReal =
      (‖(u : rootStackExtension T b)‖) ^ n := by
    rw [hfac, ENNReal.toReal_ofReal (by positivity)]
  have hlog : Real.log (distribHaarChar (rootStackExtension T b) u : Real) =
      Real.log ((rootStackHaarFactor T b u).toReal) := by
    unfold rootStackHaarFactor
    rw [ENNReal.coe_toReal]
  rw [hlog, hto, Real.log_pow]
/-- Exact E uniformizer/factor datum still needed for a direct DVR proof. -/
structure RootStackUniformizerNormData where
  uniformizer : (rootStackExtension T b)ˣ
  dvr_uniformizer : Prop
  unit_factor_one : Prop
  uniformizer_factor : Prop
  factor_norm_pow : Prop
/-- Exact required E uniformizer data. -/
def RootStackUniformizerNormDataRequired : Prop :=
  Nonempty (RootStackUniformizerNormData (l := l) T b)
/-- Exact remaining E factor-norm goal at the Qp degree. -/
def RootStackCharacterNormExactGoal : Prop :=
  RootStackHaarFactorNormPow (l := l) T b (dQpFactor (l := l) T b)
end LeanFormal.IUT.XiFPaper.S878RootStackCharacterNormDirectActual
