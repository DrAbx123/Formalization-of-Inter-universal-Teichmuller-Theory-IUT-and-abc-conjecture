import tmp.sheaf.xif.paper.S2223TateBridgeActual
import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual
import tmp.sheaf.xif.paper.S436KSideQVActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S436KSideQVActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2683S1280BaseChangeConsistencyActual

variable {l : PrimeGeFive}

/-- The source-native data with arithmetic exactly the actual S1280 Gaussian
arithmetic. This is the exact missing bridge: S1280 constructs the arithmetic,
selection and reduction, but not a full `SourceNativeInitialThetaData`. -/
def S2683NativeS1280Data : Prop :=
  ∃ T : SourceNativeInitialThetaData.{0} l, T.arithmetic = S1280Arithmetic l

/-- Conditional base-change consistency: once a source-native datum has the
actual S1280 arithmetic, its S2223 K-side curve is exactly the base change of
the S1280 `A.curve` to `K`. -/
theorem S2683_kSideCurve_eq_baseChange
    (T : SourceNativeInitialThetaData.{0} l)
    (h : T.arithmetic = S1280Arithmetic l) :
    kSideCurve T =
      (S1280Arithmetic l).curve.baseChange (S1280Arithmetic l).K := by
  cases h
  rfl

/-- Conditional consistency at the curve level (before base change). -/
theorem S2683_curve_eq
    (T : SourceNativeInitialThetaData.{0} l)
    (h : T.arithmetic = S1280Arithmetic l) :
    T.arithmetic.curve = (S1280Arithmetic l).curve := by
  cases h
  rfl

/-- Conditional consistency with the S1280 `A.curve` after collapsing the
base change, in the case `K = F`.  The hypothesis `hKF` is the missing
base-change-self identification for the concrete data. -/
theorem S2683_kSideCurve_eq_curve_of_K_eq_F
    (T : SourceNativeInitialThetaData.{0} l)
    (h : T.arithmetic = S1280Arithmetic l)
    (hKF : (S1280Arithmetic l).K = (S1280Arithmetic l).F)
    (hself : (S1280Arithmetic l).curve.baseChange (S1280Arithmetic l).K =
      (S1280Arithmetic l).curve) :
    kSideCurve T = (S1280Arithmetic l).curve := by
  rw [S2683_kSideCurve_eq_baseChange T h, hKF, hself]

#check S2683NativeS1280Data
#check S2683_kSideCurve_eq_baseChange
#check S2683_curve_eq
#check S2683_kSideCurve_eq_curve_of_K_eq_F
#print axioms S2683_kSideCurve_eq_baseChange
#print axioms S2683_curve_eq
#print axioms S2683_kSideCurve_eq_curve_of_K_eq_F

end LeanFormal.IUT.XiFPaper.S2683S1280BaseChangeConsistencyActual
end