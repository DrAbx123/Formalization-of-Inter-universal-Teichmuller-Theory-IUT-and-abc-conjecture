import tmp.sheaf.xif.paper.ThetaFunctionLineBundleActual
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourceQlThetaPunctureIdeal
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceModelBackend

/-!
# Actual source-curve theta line bundle data and divisor class

This file constructs the actual source-curve puncture line bundle module from
the actual affine Weierstrass point ideal, together with its actual
invertible/projective/rank-one proofs.  It also constructs the actual source
theta zero divisor and its actual divisor class in the backend model carrier.

The source theta function/global section and the identification of the source
theta divisor with the `{q_j^2}` divisor are not in the source contract; they
remain an exact obstruction, not a fake line bundle.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper
namespace SourceCurveThetaLineBundleActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceModelBackend
open ABCBridge.SourceThetaFunctionLineBundleActual
open ABCBridge.SourceQlThetaPunctureIdeal

universe u

variable {l : PrimeGeFive}
variable (S : SourceDefinition31Data.{u} l)

/-- The actual source theta curve. -/
abbrev actualSourceCurveThetaCurve : PuncturedEllipticCurve S.arithmetic.F :=
  actualThetaCurve (S := S)

/-- The actual affine coordinate ring of the source curve. -/
abbrev actualSourceCurveCoordinateRing : Type u :=
  sourcePunctureCoordinateRing S

/-- The actual source-curve puncture line bundle module. -/
abbrev actualSourceCurvePunctureLineBundle : Type u :=
  sourcePunctureIdealModule S

/-- The actual puncture line bundle is invertible. -/
theorem actualSourceCurvePunctureLineBundle_invertible :
    Module.Invertible (actualSourceCurveCoordinateRing S)
      (actualSourceCurvePunctureLineBundle S) :=
  sourcePunctureIdeal_invertible S

/-- The actual puncture line bundle is projective. -/
theorem actualSourceCurvePunctureLineBundle_projective :
    Module.Projective (actualSourceCurveCoordinateRing S)
      (actualSourceCurvePunctureLineBundle S) :=
  sourcePunctureIdeal_projective S

/-- The actual puncture line bundle is finite. -/
theorem actualSourceCurvePunctureLineBundle_finite :
    Module.Finite (actualSourceCurveCoordinateRing S)
      (actualSourceCurvePunctureLineBundle S) :=
  sourcePunctureIdeal_finite S

/-- The actual puncture line bundle has rank one. -/
theorem actualSourceCurvePunctureLineBundle_finrank_one :
    Module.finrank (actualSourceCurveCoordinateRing S)
      (actualSourceCurvePunctureLineBundle S) = 1 :=
  sourcePunctureIdeal_finrank_eq_one S

/-- The actual source theta zero divisor. -/
abbrev actualSourceCurveThetaZeroDivisor : actualThetaDivisorType (S := S) :=
  actualThetaZeroDivisor (S := S)

/-- The actual source theta zero divisor as a global ideal family: zero finite
part and the archimedean integer divisor coerced to real coordinates. -/
noncomputable def actualSourceCurveThetaZeroDivisorGlobalIdealFamily :
    GlobalIdealFamily S.arithmetic.F where
  finite := 0
  infinite := fun w => ((actualSourceCurveThetaZeroDivisor (S := S)) w : Real)

/-- The actual source theta zero-divisor class in the backend model carrier. -/
noncomputable def actualSourceCurveThetaZeroDivisorClass :
    Algebra.GrothendieckAddGroup (EffectiveDivisor S.arithmetic.F) :=
  idealFamilyDivisorClass (F := S.arithmetic.F)
    (actualSourceCurveThetaZeroDivisorGlobalIdealFamily S)

/-- Exact outstanding obligations: the source theta function/global section,
the identification of the global theta zero divisor with the `{q_j^2}` divisor,
and the theta line-bundle structure on the source curve are not constructed.
The list is the exact named datum; it is not a propositional gate. -/
def SourceCurveThetaFunctionLineBundleObstruction :
    ThetaFunctionLineBundleObligations (l := l) S :=
  actualThetaFunctionLineBundleObligations (l := l) S

/-- The actual puncture line bundle is the source-curve line-bundle module
constructed from the affine point ideal. -/
theorem actualSourceCurvePunctureLineBundle_eq :
    actualSourceCurvePunctureLineBundle S = sourcePunctureIdealModule S := rfl

end SourceCurveThetaLineBundleActual
end LeanFormal.IUT.XiFPaper
end
