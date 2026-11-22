/- U-L theta-pilot per-b packet: consumption of kurt's actual root carrier exports
(`urRootTheta`, `urRootTheta_ne_zero`, `urRootTheta_log_norm_eq_neg_order`,
`urRootTheta_log_norm_eq_neg_shift`, global `urRootExtensionNormedAlgebra`) on
top of `Mzk1ULThetaPacketActual`'s actual definitions and the generalized
normalized-log-mass identity.  This closes the three per-b packet theorems of
route §5.2.2 / §5.3 J1 (C1 negative term = actual theta order). -/
import tmp.sheaf.xif.paper.Mzk1URRootExtensionActual
import tmp.sheaf.xif.paper.Mzk1ULThetaPacketActual
import tmp.sheaf.xif.paper.Mzk1P6StepVBoundConsumerActual
import tmp.sheaf.xif.paper.Mzk1URRootExtInstancesActual
import Mathlib.Tactic
noncomputable section
open scoped BigOperators Pointwise
namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaPacketInstanceActual
open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1ULThetaPacketActual
open LeanFormal.IUT.XiFPaper.Mzk1URRootExtensionActual
open LeanFormal.IUT.XiFPaper.Mzk1URRootExtInstancesActual
open LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual
open MeasureTheory
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
/-- The actual per-b theta-pilot value is the log-norm of the theta value (actual
normalized Haar log-mass of the theta principal lattice). -/
theorem ulThetaPacketV_eq_log_norm (j : SignedLabel l.value) :
    ulThetaPacketV T b j = Real.log ‖urRootTheta T b j‖ := by
  unfold ulThetaPacketV ulThetaPacketRegion ulFinrankF ulThetaPacketUnitBallLog
    ulThetaPacketUnitBall
  exact urRootTheta_mass (T := T) (b := b) j
/-- The actual per-b theta-pilot value is the negative actual normalized theta
order times `log p`: this is the C1 negative term. -/
theorem ulThetaPacketV_eq_neg_order (j : SignedLabel l.value) :
    ulThetaPacketV T b j =
      -localNormOrder (qVFamTensorP T b) (urRootTheta T b j) *
        Real.log (qVFamTensorP T b : Real) := by
  unfold ulThetaPacketV ulThetaPacketRegion ulFinrankF ulThetaPacketUnitBallLog
    ulThetaPacketUnitBall
  exact urRootTheta_mass_neg_order (T := T) (b := b) j
/-- Route §5.2.2 shift form: `V_a = -(gaussExponent j/(2l)) · ord_p(q_b) · log p`. -/
theorem ulThetaPacketV_eq_neg_shift (j : SignedLabel l.value) :
    ulThetaPacketV T b j =
      -((gaussExponent j.1 : Real) / (2 * (l.value : Real))) *
        localNormOrder (qVFamTensorP T b) ((sourceRootQUnit T b : rootBase T b)) *
        Real.log (qVFamTensorP T b : Real) := by
  rw [ulThetaPacketV_eq_log_norm (T := T) (b := b) j,
    urRootTheta_log_norm_eq_neg_shift (T := T) (b := b) j]
/-- The C1-shaped upper bound for the per-b theta-pilot packet: the negative term
is the actual theta normalized order; the different-term sum and the exceptional
sum are the paper's positive contributions (supplied as nonneg side conditions,
both provable from the actual different norms and `logShellRamificationExponent_pos`). -/
theorem ulThetaPacketV_le_paperC1 (j : SignedLabel l.value)
    (exceptional : Finset qVFamTensorV)
    (hdiff : 0 ≤ ∑ i, localNormOrder (qVFamTensorP T b)
      (arithmeticTupleLocalDifferent (qVFamTensorPlaces T b) qVFamTensorTuple i))
    (hexc : 0 ≤ ∑ i ∈ exceptional, (3 + Real.log
      (logShellRamificationExponent
        (K := CommonPrimeCompletion (qVFamTensorPlaces T b i (qVFamTensorTuple i)))
        (p := qVFamTensorP T b) : Real))) :
    ulThetaPacketV T b j ≤
      (-localNormOrder (qVFamTensorP T b) (urRootTheta T b j) +
        ∑ i, localNormOrder (qVFamTensorP T b)
          (arithmeticTupleLocalDifferent (qVFamTensorPlaces T b) qVFamTensorTuple i) + 1) *
        Real.log (qVFamTensorP T b : Real) +
        ∑ i ∈ exceptional, (3 + Real.log
          (logShellRamificationExponent
            (K := CommonPrimeCompletion (qVFamTensorPlaces T b i (qVFamTensorTuple i)))
            (p := qVFamTensorP T b) : Real)) := by
  have hp1 : (1 : Real) < (qVFamTensorP T b : Real) := by
    exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).one_lt
  have hlogp : 0 < Real.log (qVFamTensorP T b : Real) := Real.log_pos hp1
  rw [ulThetaPacketV_eq_neg_order (T := T) (b := b) j]
  nlinarith [mul_nonneg hdiff hlogp.le, hexc]
/-- **C1 for the per-b theta-pilot with no side conditions**: both paper positive
contributions are the actual nonnegative different sum and the actual
nonnegative exceptional sum (`Mzk1ULThetaPacketActual.ulDifferentSum_nonneg`,
`ulExceptionalSum_nonneg`). -/
theorem ulThetaPacketV_le_paperC1_uncond (j : SignedLabel l.value)
    (exceptional : Finset qVFamTensorV) :
    ulThetaPacketV T b j ≤
      (-localNormOrder (qVFamTensorP T b) (urRootTheta T b j) +
        ∑ i, localNormOrder (qVFamTensorP T b)
          (arithmeticTupleLocalDifferent (qVFamTensorPlaces T b) qVFamTensorTuple i) + 1) *
        Real.log (qVFamTensorP T b : Real) +
        ∑ i ∈ exceptional, (3 + Real.log
          (logShellRamificationExponent
            (K := CommonPrimeCompletion (qVFamTensorPlaces T b i (qVFamTensorTuple i)))
            (p := qVFamTensorP T b) : Real)) :=
  ulThetaPacketV_le_paperC1 (T := T) (b := b) j exceptional
    (ulDifferentSum_nonneg (T := T) (b := b))
    (ulExceptionalSum_nonneg (T := T) (b := b) exceptional)
#print axioms ulThetaPacketV_eq_log_norm
#print axioms ulThetaPacketV_eq_neg_order
#print axioms ulThetaPacketV_eq_neg_shift
#print axioms ulThetaPacketV_le_paperC1
#print axioms ulThetaPacketV_le_paperC1_uncond
end LeanFormal.IUT.XiFPaper.Mzk1URThetaPacketInstanceActual
end
