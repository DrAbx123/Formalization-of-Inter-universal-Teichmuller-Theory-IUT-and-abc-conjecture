import tmp.sheaf.xif.paper.S1083ScaledUnitWitnessActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly

/-! # S1084: actual integer scaling witness for lambda-O positivity

Take N = ceil(cRoot) where cRoot = qVFamPaperRootCoefficient (order/(2l)).
The constant-N pure fractional scaling datum is built from the generator
g_i = p^N in each local factor, whose norm is p^{-N}.  Then cRoot <= N and
S1083's witness gives actual domain positivity. -/

noncomputable section
open scoped BigOperators TensorProduct Topology Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1084IntegerWitnessActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S1080PushforwardConstructionActual
open LeanFormal.IUT.XiFPaper.S1081LambdaODomainHaarActual
open LeanFormal.IUT.XiFPaper.S1082LambdaOPositivityExactActual
open LeanFormal.IUT.XiFPaper.S1083ScaledUnitWitnessActual
open LeanFormal.IUT.XiFPaper.S1079RootStackMeasureAuditActual
open MeasureTheory Topology

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- N = ceil(cRoot). -/
noncomputable def s1084N : Nat :=
  Nat.ceil (qVFamPaperRootCoefficient (l := l) T b)

/-- The constant-N generator p^N has norm p^{-N}. -/
noncomputable def s1084Generator :
    (i : qVFamTensorV) →
      CommonPrimeCompletion ((qVFamTensorPlaces T b) i (qVFamTensorTuple i)) :=
  fun i => (qVFamTensorP T b : CommonPrimeCompletion
    ((qVFamTensorPlaces T b) i (qVFamTensorTuple i))) ^ (s1084N (l := l) T b : ℤ)

theorem s1084Generator_norm (i : qVFamTensorV) :
    ‖s1084Generator (l := l) T b i‖ =
      (qVFamTensorP T b : ℝ) ^ (-((s1084N (l := l) T b : ℝ))) := by
  unfold s1084Generator
  rw [norm_prime_zpow_commonPrimeCompletion]
  rw [Padic.norm_p]
  rw [zpow_natCast, inv_pow, Real.rpow_neg (by positivity),
    Real.rpow_natCast]

/-- Constant-N pure fractional scaling data. -/
noncomputable def s1084Data :
    ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple
      (fun _ => (s1084N (l := l) T b : ℝ)) :=
  arithmeticTuplePureFractionalScalingData_ofGenerator
    (qVFamTensorPlaces T b) qVFamTensorTuple
    (fun _ => (s1084N (l := l) T b : ℝ))
    (s1084Generator (l := l) T b)
    (s1084Generator_norm (l := l) T b)

/-- cRoot <= N. -/
theorem s1084Bound (i : qVFamTensorV) :
    paperRootCoefficientFamily (l := l) T b i ≤
      (s1084N (l := l) T b : ℝ) := by
  rw [show paperRootCoefficientFamily (l := l) T b i =
      qVFamPaperRootCoefficient (l := l) T b from rfl]
  exact Nat.le_ceil _

/-- The actual integer witness. -/
noncomputable def s1084Witness :
    S1083IntegerWitness (l := l) T b where
  N := s1084N (l := l) T b
  data := s1084Data (l := l) T b
  bound := s1084Bound (l := l) T b

/-- Actual domain positivity. -/
theorem s1084DomainPositivity_actual :
    S1080DomainPositivity (l := l) T b :=
  s1083DomainPositivity_of_witness (l := l) T b
    (s1084Witness (l := l) T b)

/-- Exact remaining: only the pushforward identity. -/
def S1084ExactMinimum : Prop :=
  S1080PushforwardHullEq (l := l) T b

end LeanFormal.IUT.XiFPaper.S1084IntegerWitnessActual

end
