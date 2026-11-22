import tmp.sheaf.xif.paper.SourceThetaFunctionFromAnalyticActualAdapted
import tmp.sheaf.xif.paper.SourceCurveThetaLineBundleActualAdapted
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourceQlThetaPunctureIdeal

/-!
# Actual source-curve line bundle section versus analytic theta

This file constructs an actual nonzero section of the source-curve puncture line
bundle module from the actual affine point ideal, together with the actual
analytic theta function/section and the actual source theta zero-divisor class.

The section is a genuine source-curve line-bundle section (the point-ideal
generator X - x, or 1 at infinity).  It is not the source theta function; the
source theta function/global section identification remains the exact
obstruction below.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper
namespace SourceThetaFunctionConstructionActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceThetaGenerator
open ABCBridge.ThetaLineBundleAnalyticActual
open ABCBridge.SourceQlThetaPunctureIdeal
open LeanFormal.IUT.XiFPaper.SourceThetaFunctionFromAnalyticActualAdapted
open LeanFormal.IUT.XiFPaper.SourceCurveThetaLineBundleActualAdapted

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

/-- The actual source-curve puncture line-bundle module. -/
abbrev actualSourceCurveLineBundle : Type u :=
  sourcePunctureIdealModule S

/-- The actual nonzero source-curve line-bundle section at the affine puncture:
X - x for a finite puncture, or 1 at infinity. -/
noncomputable def actualSourceCurvePunctureSection :
    actualSourceCurveLineBundle (S := S) :=
  match h : sourcePunctureAffinePoint S with
  | .zero =>
      ⟨1, by
        rw [sourcePunctureVanishingIdeal_of_zero S h]
        exact Submodule.mem_top⟩
  | .some x y _ =>
      ⟨WeierstrassCurve.Affine.CoordinateRing.XClass
          (sourcePunctureAffineModel S) x, by
        rw [sourcePunctureVanishingIdeal_of_some S h]
        exact Ideal.subset_span (by simp)⟩

/-- The actual source-curve puncture section is nonzero. -/
theorem actualSourceCurvePunctureSection_ne_zero :
    actualSourceCurvePunctureSection (S := S) ≠ 0 := by
  unfold actualSourceCurvePunctureSection
  cases h : sourcePunctureAffinePoint S with
  | zero =>
      intro hzero
      have hval : (1 : sourcePunctureCoordinateRing S) = 0 :=
        congrArg Subtype.val hzero
      exact one_ne_zero hval
  | some x y hns =>
      intro hzero
      have hval :
          WeierstrassCurve.Affine.CoordinateRing.XClass
            (sourcePunctureAffineModel S) x = 0 :=
        congrArg Subtype.val hzero
      exact WeierstrassCurve.Affine.CoordinateRing.XClass_ne_zero
        (sourcePunctureAffineModel S) x hval

/-- The actual source theta zero divisor. -/
abbrev actualSourceThetaZeroDivisor : actualThetaDivisorType (S := S) :=
  actualThetaZeroDivisor (S := S)

/-- The actual source theta zero-divisor class. -/
noncomputable abbrev actualSourceThetaZeroDivisorClass :
    Algebra.GrothendieckAddGroup (EffectiveDivisor S.arithmetic.F) :=
  SourceCurveThetaLineBundleActualAdapted.actualSourceCurveThetaZeroDivisorClass (S := S)

/-- Exact obstruction: the source theta function/global section and its
identification with the analytic theta function/section are not supplied by the
source contract. -/
structure SourceThetaFunctionConstructionObstruction : Prop where
  analyticToSourceBaseMap : Prop
  thetaFunctionEquation : Prop
  globalSectionIdentification : Prop
  lineBundleIdentification : Prop
  thetaDivisorClassIdentification : Prop

/-- The exact missing object. -/
def SourceThetaFunctionConstructionRequired : Prop :=
  Nonempty (SourceThetaFunctionConstructionObstruction (S := S))

/-- Actual data constructed from the analytic and source-curve sides. -/
structure ActualSourceThetaFunctionConstructionData where
  analyticFunction : AnalyticThetaCarrier → Complex
  analyticFunction_eq : analyticFunction = actualAnalyticThetaFunction
  analyticSection : AnalyticThetaCarrier → AnalyticThetaCarrier × Complex
  analyticSection_eq : analyticSection = actualAnalyticThetaSection
  sourceSection : actualSourceCurveLineBundle (S := S)
  sourceSection_eq :
    sourceSection = actualSourceCurvePunctureSection (S := S)
  sourceSection_ne_zero : sourceSection ≠ 0
  sourceThetaZeroDivisorClass :
    Algebra.GrothendieckAddGroup (EffectiveDivisor S.arithmetic.F)
  sourceThetaZeroDivisorClass_eq :
    sourceThetaZeroDivisorClass = actualSourceThetaZeroDivisorClass (S := S)
  thetaFunctionObstruction : Prop
  thetaFunctionObstruction_eq :
    thetaFunctionObstruction = SourceThetaFunctionConstructionRequired (S := S)

/-- The actual construction data, with the source theta function/global section
left as the exact obstruction. -/
noncomputable def actualSourceThetaFunctionConstructionData :
    ActualSourceThetaFunctionConstructionData (S := S) where
  analyticFunction := actualAnalyticThetaFunction
  analyticFunction_eq := rfl
  analyticSection := actualAnalyticThetaSection
  analyticSection_eq := rfl
  sourceSection := actualSourceCurvePunctureSection (S := S)
  sourceSection_eq := rfl
  sourceSection_ne_zero := actualSourceCurvePunctureSection_ne_zero (S := S)
  sourceThetaZeroDivisorClass := actualSourceThetaZeroDivisorClass (S := S)
  sourceThetaZeroDivisorClass_eq := rfl
  thetaFunctionObstruction := SourceThetaFunctionConstructionRequired (S := S)
  thetaFunctionObstruction_eq := rfl

/-- The actual source-curve line-bundle section is nonzero, while the analytic
theta section is separately nonzero; their identification is the exact
obstruction. -/
theorem actualSourceThetaFunctionConstructionData_sourceSection_ne_zero :
    (actualSourceThetaFunctionConstructionData (S := S)).sourceSection ≠ 0 :=
  actualSourceCurvePunctureSection_ne_zero (S := S)

end SourceThetaFunctionConstructionActualAdapted
end LeanFormal.IUT.XiFPaper
end
