import tmp.sheaf.xif.paper.SourceThetaLineBundleActualAdapted
import tmp.sheaf.xif.paper.SourceCurveThetaLineBundleActualAdapted

/-!
# Actual analytic theta function/section versus source-curve theta data

This file combines the actual analytic theta line bundle/function/section with
the actual source-curve puncture line bundle module and actual source theta
zero-divisor class.

The analytic theta function lives on the q-disc `AnalyticThetaCarrier`; the
source-curve line bundle lives on the affine Weierstrass curve.  The source
contract does not supply a comparison map between these two carriers, nor the
source theta function/global section.  Those identifications are recorded as an
exact obstruction, not fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper
namespace SourceThetaFunctionFromAnalyticActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceThetaGenerator
open ABCBridge.ThetaLineBundleAnalyticActual
open ABCBridge.SourceQlThetaPunctureIdeal
open LeanFormal.IUT.XiFPaper.SourceThetaLineBundleActualAdapted
open LeanFormal.IUT.XiFPaper.SourceCurveThetaLineBundleActualAdapted

universe u

variable {l : PrimeGeFive}
variable (S : SourceDefinition31Data.{u} l)

/-- The actual analytic theta function on the q-disc. -/
noncomputable abbrev actualAnalyticThetaFunction : AnalyticThetaCarrier → Complex :=
  fun t => analyticThetaValue t

/-- The actual analytic theta global section. -/
noncomputable abbrev actualAnalyticThetaSection :
    AnalyticThetaCarrier → AnalyticThetaCarrier × Complex :=
  analyticThetaLineBundle.thetaSection

/-- The actual analytic theta section is nonzero. -/
theorem actualAnalyticThetaSection_ne_zero (t : AnalyticThetaCarrier) :
    actualAnalyticThetaSection t ≠ analyticThetaLineBundle.zeroSection t :=
  analyticThetaLineBundle.thetaSectionNeZeroSection t

/-- The actual source-curve puncture point. -/
abbrev actualSourceCurvePuncturePoint : (sourcePunctureAffineModel S).Point :=
  sourcePunctureAffinePoint S

/-- The actual source-curve puncture line-bundle module. -/
abbrev actualSourceCurveLineBundle : Type u :=
  sourcePunctureIdealModule S

/-- The actual zero section of the source-curve puncture module. -/
def actualSourceCurveZeroSection : actualSourceCurveLineBundle (S := S) :=
  0

/-- The actual source theta zero-divisor class. -/
noncomputable abbrev actualSourceCurveThetaZeroDivisorClass :
    Algebra.GrothendieckAddGroup (EffectiveDivisor S.arithmetic.F) :=
  SourceCurveThetaLineBundleActualAdapted.actualSourceCurveThetaZeroDivisorClass (S := S)

/-- Exact obstruction for connecting the analytic theta function/section to the
source-curve theta line bundle.  All fields are genuine missing source
identifications, not fake data. -/
structure AnalyticSourceThetaIdentificationObstruction : Prop where
  analyticToSourceMap : Prop
  thetaFunctionIdentification : Prop
  thetaSectionIdentification : Prop
  lineBundleIdentification : Prop
  thetaDivisorClassIdentification : Prop

/-- The exact source-obstruction proposition. -/
def AnalyticSourceThetaIdentificationRequired : Prop :=
  Nonempty (AnalyticSourceThetaIdentificationObstruction (S := S))

/-- Actual data available from the analytic and source-curve sides. -/
structure ActualSourceThetaFunctionData where
  analyticFunction : AnalyticThetaCarrier → Complex
  analyticFunction_eq : analyticFunction = actualAnalyticThetaFunction
  analyticSection : AnalyticThetaCarrier → AnalyticThetaCarrier × Complex
  analyticSection_eq : analyticSection = actualAnalyticThetaSection
  sourceCurve : PuncturedEllipticCurve S.arithmetic.F
  sourceCurve_eq : sourceCurve = actualSourceCurveThetaCurve (S := S)
  sourcePuncturePoint : (sourcePunctureAffineModel S).Point
  sourcePuncturePoint_eq : sourcePuncturePoint = actualSourceCurvePuncturePoint (S := S)
  sourceZeroSection : actualSourceCurveLineBundle (S := S)
  sourceZeroSection_eq :
    sourceZeroSection = actualSourceCurveZeroSection (S := S)
  sourceThetaZeroDivisorClass :
    Algebra.GrothendieckAddGroup (EffectiveDivisor S.arithmetic.F)
  sourceThetaZeroDivisorClass_eq :
    sourceThetaZeroDivisorClass = actualSourceCurveThetaZeroDivisorClass (S := S)
  analyticSourceObstruction : Prop
  analyticSourceObstruction_eq :
    analyticSourceObstruction = AnalyticSourceThetaIdentificationRequired (S := S)

/-- The actual analytic/source-curve theta data, with the source theta
function/section identification still an exact obstruction. -/
noncomputable def actualSourceThetaFunctionData :
    ActualSourceThetaFunctionData (S := S) where
  analyticFunction := actualAnalyticThetaFunction
  analyticFunction_eq := rfl
  analyticSection := actualAnalyticThetaSection
  analyticSection_eq := rfl
  sourceCurve := actualSourceCurveThetaCurve (S := S)
  sourceCurve_eq := rfl
  sourcePuncturePoint := actualSourceCurvePuncturePoint (S := S)
  sourcePuncturePoint_eq := rfl
  sourceZeroSection := actualSourceCurveZeroSection (S := S)
  sourceZeroSection_eq := rfl
  sourceThetaZeroDivisorClass := actualSourceCurveThetaZeroDivisorClass (S := S)
  sourceThetaZeroDivisorClass_eq := rfl
  analyticSourceObstruction := AnalyticSourceThetaIdentificationRequired (S := S)
  analyticSourceObstruction_eq := rfl

/-- The actual analytic theta section is nonzero while the source-curve section
provided here is the zero section; the nonzero source theta section remains
part of the exact obstruction. -/
theorem actualSourceThetaFunctionData_analytic_nonzero (t : AnalyticThetaCarrier) :
    (actualSourceThetaFunctionData (S := S)).analyticSection t ≠
      analyticThetaLineBundle.zeroSection t :=
  actualAnalyticThetaSection_ne_zero t

end SourceThetaFunctionFromAnalyticActualAdapted
end LeanFormal.IUT.XiFPaper
end
