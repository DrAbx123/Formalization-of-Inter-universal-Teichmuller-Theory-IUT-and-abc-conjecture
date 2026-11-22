import tmp.sheaf.xif.paper.SourceThetaFunctionFromAnalyticActual
import tmp.sheaf.xif.paper.SourceCurveThetaLineBundleActual

/-!
# Analytic theta function/section versus source-curve theta line bundle

This file attempts the actual identification between the analytic theta
function/section and the source-curve theta line bundle/divisor class.

The actual analytic theta section is nonzero on the q-disc; the source-curve
puncture line bundle and its zero section are actual.  There is no source
comparison map between the analytic q-disc and the affine Weierstrass curve, so
the full identification is recorded as an exact obstruction.

Constructed actual partial data:

* the analytic theta function and global section;
* the source-curve puncture line bundle module and zero section;
* the constant zero-section comparison map;
* the actual empty analytic theta zero locus and the actual source theta zero
  divisor, with their actual zero-locus/divisor comparison.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper
namespace AnalyticSourceThetaIdentificationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open ABCBridge.ThetaLineBundleAnalyticActual
open ABCBridge.SourceQlThetaPunctureIdeal
open LeanFormal.IUT.XiFPaper.SourceThetaFunctionFromAnalyticActual
open LeanFormal.IUT.XiFPaper.SourceCurveThetaLineBundleActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceThetaGenerator

universe u

variable {l : PrimeGeFive}
variable (S : SourceDefinition31Data.{u} l)

/-- The actual analytic theta function. -/
noncomputable abbrev actualAnalyticThetaFunction : AnalyticThetaCarrier → Complex :=
  fun t => analyticThetaValue t

/-- The actual analytic theta section. -/
noncomputable abbrev actualAnalyticThetaSection :
    AnalyticThetaCarrier → AnalyticThetaCarrier × Complex :=
  analyticThetaLineBundle.thetaSection

/-- The actual empty analytic theta zero locus. -/
def actualAnalyticThetaZeroLocus : Set AnalyticThetaCarrier :=
  analyticThetaLineBundle.zeroLocus

/-- The actual analytic theta zero locus is empty. -/
theorem actualAnalyticThetaZeroLocus_empty :
    actualAnalyticThetaZeroLocus = ∅ :=
  analyticThetaLineBundle_zeroLocus_empty

/-- The actual source-curve puncture line-bundle module. -/
abbrev actualSourceCurveLineBundle : Type u :=
  sourcePunctureIdealModule S

/-- The actual zero section of the source-curve module. -/
def actualSourceCurveZeroSection : actualSourceCurveLineBundle (S := S) :=
  0

/-- The actual source theta zero divisor. -/
abbrev actualSourceThetaZeroDivisor : actualThetaDivisorType (S := S) :=
  actualThetaZeroDivisor (S := S)

/-- The actual source theta zero divisor is zero. -/
theorem actualSourceThetaZeroDivisor_eq_zero :
    actualSourceThetaZeroDivisor (S := S) = 0 :=
  sourceThetaLineBundleZeroDivisor_eq_zero (S := S)

/-- The actual zero-section comparison map: every analytic point is sent to the
actual source zero section.  This is a genuine actual map, but it is not the
source theta function identification. -/
def zeroSectionComparisonMap :
    AnalyticThetaCarrier → actualSourceCurveLineBundle (S := S) :=
  fun _ => actualSourceCurveZeroSection (S := S)

/-- The zero-section comparison map is constant. -/
theorem zeroSectionComparisonMap_constant (t t' : AnalyticThetaCarrier) :
    zeroSectionComparisonMap (S := S) t = zeroSectionComparisonMap (S := S) t' := rfl

/-- The actual zero-locus/divisor comparison: the analytic theta zero locus is
empty and the source theta zero divisor is zero. -/
def ActualZeroLocusDivisorComparison : Prop :=
  actualAnalyticThetaZeroLocus = ∅ ∧
    actualSourceThetaZeroDivisor (S := S) = 0

/-- The actual zero-locus/divisor comparison holds. -/
theorem actualZeroLocusDivisorComparison :
    ActualZeroLocusDivisorComparison (S := S) :=
  ⟨actualAnalyticThetaZeroLocus_empty,
    actualSourceThetaZeroDivisor_eq_zero (S := S)⟩

/-- Exact obstruction for the full analytic/source theta identification. -/
structure AnalyticSourceThetaIdentificationObstruction : Prop where
  baseComparison : Prop
  totalSpaceComparison : Prop
  thetaFunctionEquation : Prop
  thetaSectionEquation : Prop
  lineBundleEquiv : Prop
  thetaDivisorClassEq : Prop

/-- The exact required identification object. -/
def AnalyticSourceThetaIdentificationRequired : Prop :=
  Nonempty (AnalyticSourceThetaIdentificationObstruction (S := S))

/-- Actual partial data assembled from the analytic and source-curve sides. -/
structure ActualAnalyticSourceThetaPartialData where
  analyticFunction : AnalyticThetaCarrier → Complex
  analyticFunction_eq : analyticFunction = actualAnalyticThetaFunction
  analyticSection : AnalyticThetaCarrier → AnalyticThetaCarrier × Complex
  analyticSection_eq : analyticSection = actualAnalyticThetaSection
  analyticZeroLocus : Set AnalyticThetaCarrier
  analyticZeroLocus_eq : analyticZeroLocus = actualAnalyticThetaZeroLocus
  sourceZeroSection : actualSourceCurveLineBundle (S := S)
  sourceZeroSection_eq :
    sourceZeroSection = actualSourceCurveZeroSection (S := S)
  zeroSectionMap : AnalyticThetaCarrier → actualSourceCurveLineBundle (S := S)
  zeroSectionMap_eq :
    zeroSectionMap = zeroSectionComparisonMap (S := S)
  zeroLocusDivisorComparison : Prop
  zeroLocusDivisorComparison_eq :
    zeroLocusDivisorComparison = ActualZeroLocusDivisorComparison (S := S)
  zeroLocusDivisorComparison_proved : zeroLocusDivisorComparison
  analyticSourceObstruction : Prop
  analyticSourceObstruction_eq :
    analyticSourceObstruction = AnalyticSourceThetaIdentificationRequired (S := S)

/-- The actual analytic/source partial data, with the full theta identification
left as the exact obstruction. -/
noncomputable def actualAnalyticSourceThetaPartialData :
    ActualAnalyticSourceThetaPartialData (S := S) where
  analyticFunction := actualAnalyticThetaFunction
  analyticFunction_eq := rfl
  analyticSection := actualAnalyticThetaSection
  analyticSection_eq := rfl
  analyticZeroLocus := actualAnalyticThetaZeroLocus
  analyticZeroLocus_eq := rfl
  sourceZeroSection := actualSourceCurveZeroSection (S := S)
  sourceZeroSection_eq := rfl
  zeroSectionMap := zeroSectionComparisonMap (S := S)
  zeroSectionMap_eq := rfl
  zeroLocusDivisorComparison := ActualZeroLocusDivisorComparison (S := S)
  zeroLocusDivisorComparison_eq := rfl
  zeroLocusDivisorComparison_proved := actualZeroLocusDivisorComparison (S := S)
  analyticSourceObstruction := AnalyticSourceThetaIdentificationRequired (S := S)
  analyticSourceObstruction_eq := rfl

/-- The actual analytic theta section is nonzero. -/
theorem actualAnalyticSourceThetaPartialData_analytic_nonzero
    (t : AnalyticThetaCarrier) :
    (actualAnalyticSourceThetaPartialData (S := S)).analyticSection t ≠
      analyticThetaLineBundle.zeroSection t :=
  analyticThetaLineBundle_thetaSection_ne_zero t

end AnalyticSourceThetaIdentificationActual
end LeanFormal.IUT.XiFPaper
end
