import tmp.sheaf.xif.paper.ThetaLineBundleAnalyticActualAdapted
import tmp.sheaf.xif.paper.ThetaFunctionLineBundleActual

/-!
# Actual source theta line bundle and theta section

The project has a genuine analytic theta line bundle on the q-disc, with the
actual analytic theta function as its global section.  It does not have the
source-curve theta line bundle, the etale theta function, or the global theta
divisor identified with the `{q_j^2}` divisor.

This file constructs the actual analytic line bundle/function/section objects,
the actual source theta curve/divisor-type/zero-divisor objects, and records the
source-curve theta line-bundle obstruction exactly.  No source line bundle or
theta global section is fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper
namespace SourceThetaLineBundleActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceThetaGenerator
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceThetaDivisor
open ABCBridge.ThetaLineBundleAnalyticActualAdapted
open ABCBridge.SourceThetaFunctionLineBundleActual
open ABCBridge.SourceQlThetaLineBundleFromCurve

universe u

variable {l : PrimeGeFive}
variable (S : SourceDefinition31Data.{u} l)

/-- The actual analytic theta line bundle on the q-disc. -/
noncomputable abbrev actualAnalyticThetaLineBundle : AnalyticThetaLineBundle :=
  analyticThetaLineBundle

/-- The actual analytic theta function. -/
noncomputable def actualAnalyticThetaFunction : AnalyticThetaCarrier -> Complex :=
  fun t => analyticThetaValue t

/-- The actual analytic theta global section. -/
noncomputable def actualAnalyticThetaSection :
    AnalyticThetaCarrier -> AnalyticThetaCarrier × Complex :=
  analyticThetaLineBundle.thetaSection

/-- The actual analytic theta section is the graph of the analytic theta
function. -/
theorem actualAnalyticThetaSection_eq (t : AnalyticThetaCarrier) :
    actualAnalyticThetaSection t = (t, actualAnalyticThetaFunction t) := rfl

/-- The actual analytic theta section is nowhere zero. -/
theorem actualAnalyticThetaSection_ne_zero (t : AnalyticThetaCarrier) :
    actualAnalyticThetaSection t ≠ analyticThetaLineBundle.zeroSection t :=
  analyticThetaLineBundle.thetaSectionNeZeroSection t

/-- The actual analytic theta section has empty zero locus on the q-disc. -/
theorem actualAnalyticThetaSection_zeroLocus_empty :
    analyticThetaLineBundle.zeroLocus = ∅ :=
  analyticThetaLineBundle_zeroLocus_empty

/-- The actual source theta curve. -/
abbrev actualSourceThetaCurve : PuncturedEllipticCurve S.arithmetic.F :=
  actualThetaCurve (S := S)

/-- The actual source theta-divisor type. -/
abbrev actualSourceThetaDivisorType : Type u :=
  actualThetaDivisorType (S := S)

/-- The actual source theta zero divisor. -/
noncomputable def actualSourceThetaZeroDivisor : actualSourceThetaDivisorType (S := S) :=
  actualThetaZeroDivisor (S := S)

/-- The actual source theta zero divisor is zero. -/
theorem actualSourceThetaZeroDivisor_eq_zero :
    actualSourceThetaZeroDivisor (S := S) = 0 :=
  sourceThetaLineBundleZeroDivisor_eq_zero (S := S)

/-- Exact outstanding obligations: the source-curve theta line bundle, the theta
object and theta function/global section, and the global theta zero divisor
identified with the `{q_j^2}` divisor are not in the source contract.  The list
is the exact named datum; it is not a propositional gate. -/
def SourceThetaCurveLineBundleObstruction :
    ThetaFunctionLineBundleObligations (l := l) S :=
  actualThetaFunctionLineBundleObligations (l := l) S

/-- Actual combined data: the actual analytic theta line bundle/function/section,
the actual source theta curve/divisor-type/zero-divisor, and the exact source
line-bundle obstruction. -/
structure ActualSourceThetaLineBundleData where
  analyticLineBundle : AnalyticThetaLineBundle
  analyticLineBundle_eq : analyticLineBundle = actualAnalyticThetaLineBundle
  analyticThetaFunction : AnalyticThetaCarrier -> Complex
  analyticThetaFunction_eq : analyticThetaFunction = actualAnalyticThetaFunction
  analyticThetaSection : AnalyticThetaCarrier -> (AnalyticThetaCarrier × Complex)
  analyticThetaSection_eq : analyticThetaSection = actualAnalyticThetaSection
  sourceThetaCurve : PuncturedEllipticCurve S.arithmetic.F
  sourceThetaCurve_eq : sourceThetaCurve = actualSourceThetaCurve (S := S)
  sourceThetaZeroDivisor : actualSourceThetaDivisorType (S := S)
  sourceThetaZeroDivisor_eq :
    sourceThetaZeroDivisor = actualSourceThetaZeroDivisor (S := S)
  sourceThetaZeroDivisor_zero : sourceThetaZeroDivisor = 0
  sourceThetaLineBundleObstruction :
    ThetaFunctionLineBundleObligations (l := l) S
  sourceThetaLineBundleObstruction_eq :
    sourceThetaLineBundleObstruction = SourceThetaCurveLineBundleObstruction (S := S)

/-- The actual combined source theta line-bundle data. -/
noncomputable def actualSourceThetaLineBundleData :
    ActualSourceThetaLineBundleData (S := S) where
  analyticLineBundle := actualAnalyticThetaLineBundle
  analyticLineBundle_eq := rfl
  analyticThetaFunction := actualAnalyticThetaFunction
  analyticThetaFunction_eq := rfl
  analyticThetaSection := actualAnalyticThetaSection
  analyticThetaSection_eq := rfl
  sourceThetaCurve := actualSourceThetaCurve (S := S)
  sourceThetaCurve_eq := rfl
  sourceThetaZeroDivisor := actualSourceThetaZeroDivisor (S := S)
  sourceThetaZeroDivisor_eq := rfl
  sourceThetaZeroDivisor_zero := actualSourceThetaZeroDivisor_eq_zero (S := S)
  sourceThetaLineBundleObstruction := SourceThetaCurveLineBundleObstruction (S := S)
  sourceThetaLineBundleObstruction_eq := rfl

/-- The actual analytic section is nowhere zero. -/
theorem actualSourceThetaLineBundleData_section_ne_zero
    (t : AnalyticThetaCarrier) :
    (actualSourceThetaLineBundleData (S := S)).analyticThetaSection t ≠
      (actualSourceThetaLineBundleData (S := S)).analyticLineBundle.zeroSection t :=
  actualAnalyticThetaSection_ne_zero t

end SourceThetaLineBundleActualAdapted
end LeanFormal.IUT.XiFPaper
end
