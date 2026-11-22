import tmp.sheaf.xif.paper.S1536SourceSignQuotientFromOrbicurveActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36OrbicurveFeasibility
/-! # S1555: actual [-1] involution on the curve; exact missing lift to xF
The concrete punctured elliptic curve of Example36 carries the actual
[-1]-involution with laws (involutive, fixes puncture, nontrivial).  That is an
automorphism of the curve-point group, NOT a morphism of the S1419 orbicurve
HyperbolicOrbicurve.Hom.  The exact first missing field is the geometric lift
  ellipticInvolution : xF.Hom xF
together with its square/uniqueness and the OrbicurveSignAction.  No fake Hom
is constructed. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S1555EllipticInvolutionActual
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36.OrbicurveFeasibility
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
variable {l : PrimeGeFive}
/-- The actual -1 involution on the concrete curve-point group. -/
noncomputable def S1555CurveInvolution :
    concretePuncturedCurve.curve.toProjective.Point →+
      concretePuncturedCurve.curve.toProjective.Point :=
  curveInvolutionAddEquiv concretePuncturedCurve
theorem S1555CurveInvolution_involutive :
    Function.Involutive (S1555CurveInvolution) :=
  curveInvolution_involutive concretePuncturedCurve
theorem S1555CurveInvolution_nontrivial :
    S1555CurveInvolution pointTwoThree ≠ pointTwoThree :=
  curveInvolution_nontrivial
theorem S1555CurveInvolution_fixes_puncture :
    S1555CurveInvolution concretePuncturedCurve.puncture =
      concretePuncturedCurve.puncture :=
  curveInvolution_fixes_origin
/-- Exact first missing field: the geometric lift of the curve involution to
an actual endomorphism of the S1419 orbicurve. -/
abbrev S1555MissingGeometricInvolution : Type 1 :=
  (S1536XF (l := l)).Hom (S1536XF (l := l))
-- Also missing: TwoIso(square,id), uniqueness, and OrbicurveSignAction.
end LeanFormal.IUT.XiFPaper.S1555EllipticInvolutionActual
