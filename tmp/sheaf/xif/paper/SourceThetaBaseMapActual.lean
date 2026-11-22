import tmp.sheaf.xif.paper.SourceThetaFunctionConstructionActual
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourceQlThetaPunctureIdeal

/-!
# Analytic theta carrier → source curve base map candidate

This file constructs the actual analytic theta carrier and the actual source
affine puncture point, and the literal constant base-map candidate

`fun _ => sourcePunctureAffinePoint S`.

It also records the exact obstruction: the source contract does not supply a
nonconstant analytic-to-source base map, a source theta function/global section,
or the theta function equation.  The constant map is not asserted to be the
paper base map.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper
namespace SourceThetaBaseMapActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceThetaGenerator
open ABCBridge.ThetaLineBundleAnalyticActual
open ABCBridge.SourceQlThetaPunctureIdeal
open LeanFormal.IUT.XiFPaper.SourceThetaFunctionConstructionActual

universe u

variable {l : PrimeGeFive}
variable (S : SourceDefinition31Data.{u} l)

/-- The actual analytic theta carrier (q-disc). -/
abbrev actualAnalyticThetaBase : Type :=
  AnalyticThetaCarrier

/-- The actual analytic theta function. -/
noncomputable abbrev actualAnalyticThetaFunction : actualAnalyticThetaBase → Complex :=
  fun t => analyticThetaValue t

/-- The actual source affine curve point type. -/
abbrev actualSourceAffineCurvePoint : Type :=
  (sourcePunctureAffineModel S).Point

/-- The actual source puncture point. -/
noncomputable abbrev actualSourcePuncturePoint : actualSourceAffineCurvePoint (S := S) :=
  sourcePunctureAffinePoint S

/-- The literal constant analytic-to-source base-map candidate.  This is an
actual map, but it is not claimed to be the paper's analytic-to-source
identification. -/
def analyticToSourceBaseMapCandidate :
    actualAnalyticThetaBase → actualSourceAffineCurvePoint (S := S) :=
  fun _ => actualSourcePuncturePoint (S := S)

/-- The constant base-map candidate is constant. -/
theorem analyticToSourceBaseMapCandidate_constant
    (t t' : actualAnalyticThetaBase) :
    analyticToSourceBaseMapCandidate (S := S) t =
      analyticToSourceBaseMapCandidate (S := S) t' := rfl

/-- The constant candidate hits the actual source puncture point. -/
theorem analyticToSourceBaseMapCandidate_apply
    (t : actualAnalyticThetaBase) :
    analyticToSourceBaseMapCandidate (S := S) t =
      actualSourcePuncturePoint (S := S) := rfl

/-- Exact obstruction for the analytic-to-source base map and theta function
equation. -/
structure SourceThetaBaseMapObstruction : Prop where
  nonconstantBaseMap : Prop
  baseMapCompatibility : Prop
  sourceThetaFunction : Prop
  thetaFunctionEquation : Prop
  globalSectionIdentification : Prop

/-- The exact required object. -/
def SourceThetaBaseMapRequired : Prop :=
  Nonempty (SourceThetaBaseMapObstruction (S := S))

/-- Actual data available from the analytic and source-curve sides. -/
structure ActualSourceThetaBaseMapData where
  analyticFunction : actualAnalyticThetaBase → Complex
  analyticFunction_eq : analyticFunction = actualAnalyticThetaFunction
  sourcePuncturePoint : actualSourceAffineCurvePoint (S := S)
  sourcePuncturePoint_eq :
    sourcePuncturePoint = actualSourcePuncturePoint (S := S)
  baseMapCandidate : actualAnalyticThetaBase → actualSourceAffineCurvePoint (S := S)
  baseMapCandidate_eq :
    baseMapCandidate = analyticToSourceBaseMapCandidate (S := S)
  baseMapCandidate_constant :
    forall t t', baseMapCandidate t = baseMapCandidate t'
  baseMapObstruction : Prop
  baseMapObstruction_eq :
    baseMapObstruction = SourceThetaBaseMapRequired (S := S)

/-- The actual analytic/source base-map construction data, with the paper base
map/theta equation left as the exact obstruction. -/
noncomputable def actualSourceThetaBaseMapData :
    ActualSourceThetaBaseMapData (S := S) where
  analyticFunction := actualAnalyticThetaFunction
  analyticFunction_eq := rfl
  sourcePuncturePoint := actualSourcePuncturePoint (S := S)
  sourcePuncturePoint_eq := rfl
  baseMapCandidate := analyticToSourceBaseMapCandidate (S := S)
  baseMapCandidate_eq := rfl
  baseMapCandidate_constant := analyticToSourceBaseMapCandidate_constant (S := S)
  baseMapObstruction := SourceThetaBaseMapRequired (S := S)
  baseMapObstruction_eq := rfl

/-- The actual constant base-map candidate is literal. -/
theorem actualSourceThetaBaseMapData_baseMapCandidate
    (t : actualAnalyticThetaBase) :
    (actualSourceThetaBaseMapData (S := S)).baseMapCandidate t =
      actualSourcePuncturePoint (S := S) := rfl

end SourceThetaBaseMapActual
end LeanFormal.IUT.XiFPaper
end
