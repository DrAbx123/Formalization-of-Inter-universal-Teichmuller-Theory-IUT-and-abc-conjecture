import tmp.sheaf.xif.paper.Mzk1RouteC0RootQLatticeV2Actual
import tmp.sheaf.xif.paper.PaperRootExtensionFieldScalingActual
import tmp.sheaf.xif.paper.PaperRootExtensionHaarActual
import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
/-! #A1.6 final signed readout at one actual qVFam block (self-contained).

`qhatLogReadout = (1/d_F)(log mu(qhatLattice) - log mu(O))` and the explicit
`a1Delta = log(rootImageRadius) - qhatLogReadout`; we prove `0 <= a1Delta` from
`c0QLattice subset rootThetaFieldLambdaO` and the actual ball mass formula.
Hence `qhatLogReadout <= log||lambda||`, and the lambda-ball readout is exactly
`log||lambda||`. No comparison or delta-small hypothesis is used. -/
noncomputable section
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1A1SignedReadoutFinalActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeV2Actual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionFieldScalingActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable (b : Bad (nativePlaceSelection T))
variable [Fintype (Bad (nativePlaceSelection T))]
local instance measurableSpaceRootExtension :
    MeasurableSpace (rootNormedExtension T b) :=
  rootNormedExtensionMeasurableSpace (T := T) (b := b)
local instance borelSpaceRootExtension :
    BorelSpace (rootNormedExtension T b) := ⟨rfl⟩
/-- Signed normalized log-mass readout of the actual qhat-lattice relative to O. -/
noncomputable def qhatLogReadout : Real :=
  (1 / (s1915LocalDegree T b : Real)) *
    (Real.log (rootExtensionHaar T b (c0QLattice T b)).toReal -
      Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal)
/-- Explicit A1.6 delta. -/
noncomputable def a1DeltaExplicit : Real :=
  Real.log (rootImageRadius T b : Real) - qhatLogReadout T b
/-- Actual lambda-ball mass formula. -/
theorem lambdaBall_measure_eq :
    rootExtensionHaar T b (rootThetaFieldLambdaO T b) =
      ENNReal.ofReal ((rootImageRadius T b : Real) ^ s1915LocalDegree T b) *
        rootExtensionHaar T b (rootExtensionUnitBall T b) := by
  rw [rootThetaFieldLambdaO_eq_closedBall]
  simpa [rootImageRadius_eq_norm_fieldLambda] using s1915_local_measure T b
/-- A1.6 signed bound: delta is nonnegative. -/
theorem a1DeltaExplicit_nonneg
    (hd : 0 < s1915LocalDegree T b)
    (hQ0 : rootExtensionHaar T b (c0QLattice T b) ≠ 0)
    (hQtop : rootExtensionHaar T b (c0QLattice T b) ≠ ⊤)
    (hO0 : rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ 0)
    (hOtop : rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ ⊤) :
    0 ≤ a1DeltaExplicit T b := by
  have hdpos : (0 : Real) < (s1915LocalDegree T b : Real) := by exact_mod_cast hd
  have hrpos : (0 : Real) < (rootImageRadius T b : Real) := by
    exact_mod_cast rootImageRadius_pos (T := T) (b := b)
  have hOpos : 0 < (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal :=
    ENNReal.toReal_pos hO0 hOtop
  have hQpos : 0 < (rootExtensionHaar T b (c0QLattice T b)).toReal :=
    ENNReal.toReal_pos hQ0 hQtop
  have hμle := measure_mono (c0QLattice_subset_lambda T b)
  have htop : rootExtensionHaar T b (rootThetaFieldLambdaO T b) < ⊤ := by
    rw [lambdaBall_measure_eq T b]
    exact ENNReal.mul_lt_top ENNReal.one_ne_top
      (rootExtensionUnitBall_measure_lt_top T b).ne
  have hle_real := ENNReal.toReal_mono htop.ne hμle
  have hlog := Real.log_le_log hQpos hle_real
  have hlambdaLog :
      Real.log (rootExtensionHaar T b (rootThetaFieldLambdaO T b)).toReal =
        (s1915LocalDegree T b : Real) * Real.log (rootImageRadius T b : Real) +
          Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal := by
    rw [lambdaBall_measure_eq T b]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    rw [Real.log_mul (by positivity) hOpos.ne']
    rw [Real.log_pow]
  have hA : Real.log (rootExtensionHaar T b (c0QLattice T b)).toReal ≤
      (s1915LocalDegree T b : Real) * Real.log (rootImageRadius T b : Real) +
        Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal :=
    le_trans hlog (le_of_eq hlambdaLog)
  have hdiff : Real.log (rootExtensionHaar T b (c0QLattice T b)).toReal -
      Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal ≤
      (s1915LocalDegree T b : Real) * Real.log (rootImageRadius T b : Real) := by
    linarith
  have hreadout : qhatLogReadout T b ≤ Real.log (rootImageRadius T b : Real) := by
    unfold qhatLogReadout
    have hcalc : (1 / (s1915LocalDegree T b : Real)) *
        (Real.log (rootExtensionHaar T b (c0QLattice T b)).toReal -
          Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal) =
        ((Real.log (rootExtensionHaar T b (c0QLattice T b)).toReal -
          Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal) /
          (s1915LocalDegree T b : Real)) := by ring
    rw [hcalc]
    rw [div_le_iff₀ hdpos]
    linarith
  unfold a1DeltaExplicit
  linarith
end LeanFormal.IUT.XiFPaper.Mzk1A1SignedReadoutFinalActual
end