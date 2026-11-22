import tmp.sheaf.xif.paper.S1484ThetaObjectActual
/-! # S1582: actual geometric theta divisor and exact q comparison gap
This file records the actual curve-level geometric theta divisor as the zero
divisor of the S1484 theta section at an affine point: the point divisor [P],
degree 1.  The q_v^(j^2) family is a family of nonzero real units, not a curve
divisor; the exact missing object is its scalar comparison with the theta
section value, not a weighted point divisor. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace ABCBridge.S1582GeometricThetaDivisorActual
open LeanFormal.IUT LeanFormal.IUT.Theorem311Source
open ABCBridge.S1484ThetaObjectActual
open ABCBridge.SourceQlThetaPunctureIdeal
open ABCBridge.S1423ThetaInvertibleActual
open ABCBridge.SourceQlThetaLineBundleFromCurve
open ABCBridge.S1424ThetaSectionActual
universe u
variable {l : PrimeGeFive} (S : SourceDefinition31Data.{u} l)
/-- The actual geometric theta divisor at an affine puncture: the zero divisor
of the S1484 theta section, i.e. the point divisor [P]. -/
noncomputable abbrev geometricThetaDivisorAt {x y : S.arithmetic.F}
    (h : (s1423Model S).Nonsingular x y) : s1484CurveDivisor S :=
  s1484ThetaZeroDivisorAt S h
@[simp] theorem geometricThetaDivisorAt_apply_self
    {x y : S.arithmetic.F} (h : (s1423Model S).Nonsingular x y) :
    geometricThetaDivisorAt S h
      (WeierstrassCurve.Affine.Point.some x y h) = 1 :=
  s1484ThetaZeroDivisorAt_apply_self S h
theorem geometricThetaDivisorAt_degree
    {x y : S.arithmetic.F} (h : (s1423Model S).Nonsingular x y) :
    s1484DivisorDegree S (geometricThetaDivisorAt S h) = 1 := by
  rw [geometricThetaDivisorAt, s1484ThetaZeroDivisorAt]
  exact s1484DivisorDegree_single S _ 1
end ABCBridge.S1582GeometricThetaDivisorActual
end
