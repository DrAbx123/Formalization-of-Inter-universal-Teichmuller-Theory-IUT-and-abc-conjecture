import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientBridgeActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S742SpectralOrderFactorActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The paper-faithful order coefficient. -/
noncomputable def paperOrderCoefficient : Real :=
  ((qVFamily T b).order : Real)

/-- The spectral supply coefficient. -/
noncomputable def spectralCoefficient : Real :=
  QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b

/-- Exact equality question: is the spectral coefficient the paper order? -/
def SpectralCoefficientEqualsOrder : Prop :=
  spectralCoefficient T b = paperOrderCoefficient T b

/-- Exact factor relation for the spectral-vs-order coefficient difference. -/
theorem spectral_sub_order_mul_log_eq :
    (spectralCoefficient T b - paperOrderCoefficient T b) *
        Real.log (qVFamTensorP T b : Real) =
      paperOrderCoefficient T b *
        (Real.log (residueNormBase (qVFamTensorPlace T b)) -
          Real.log (qVFamTensorP T b : Real)) -
        Real.log (qVFamNormRatio T b) := by
  have h := qVFamNormalizedCoefficient_mul_log_eq_order_mul_log_residueNormBase_sub_log_ratio
    (l := l) T b
  unfold spectralCoefficient paperOrderCoefficient
  rw [qVFamNormalizedCoefficient_eq (l := l) T b] at h
  nlinarith

/-- Exact correction condition for spectral = order. -/
def SpectralOrderCorrection : Prop :=
  paperOrderCoefficient T b *
      (Real.log (residueNormBase (qVFamTensorPlace T b)) -
        Real.log (qVFamTensorP T b : Real)) =
    Real.log (qVFamNormRatio T b)

/-- Spectral coefficient equals paper order iff the exact residue-norm/ratio
correction vanishes. -/
theorem spectralCoefficientEqualsOrder_iff_correction :
    SpectralCoefficientEqualsOrder T b ↔ SpectralOrderCorrection (l := l) T b := by
  have hfac := spectral_sub_order_mul_log_eq (l := l) T b
  have hprime : Nat.Prime (qVFamTensorP T b) := Fact.out
  have hp1 : (1 : Real) < (qVFamTensorP T b : Real) := by exact_mod_cast hprime.one_lt
  have hlog : Real.log (qVFamTensorP T b : Real) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (lt_trans zero_lt_one hp1) (ne_of_gt hp1)
  unfold SpectralCoefficientEqualsOrder SpectralOrderCorrection
  constructor
  · intro h
    have h0 : (spectralCoefficient T b - paperOrderCoefficient T b) = 0 := sub_eq_zero.mpr h
    rw [h0, zero_mul] at hfac
    linarith
  · intro h
    have hzero : (spectralCoefficient T b - paperOrderCoefficient T b) *
        Real.log (qVFamTensorP T b : Real) = 0 := by
      rw [hfac, h]; ring
    exact sub_eq_zero.mp (mul_eq_zero.mp hzero |>.resolve_right hlog)

/-- Exact minimal remaining datum: the correction condition. -/
def SpectralOrderCorrectionRequired : Prop :=
  SpectralOrderCorrection (l := l) T b

/-- Equality would follow from normalized/residue norm coincidence. -/
theorem spectralCoefficientEqualsOrder_of_correction
    (h : SpectralOrderCorrection (l := l) T b) :
    SpectralCoefficientEqualsOrder T b :=
  (spectralCoefficientEqualsOrder_iff_correction (l := l) T b).mpr h

end LeanFormal.IUT.XiFPaper.S742SpectralOrderFactorActual

end
