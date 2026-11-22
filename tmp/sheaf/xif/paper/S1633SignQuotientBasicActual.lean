import tmp.sheaf.xif.paper.S1555EllipticInvolutionActual

/-! # S1633: SourceSignQuotientData basic parts: exact first missing stack lift

Actual from S1555 (curve-point level):
* `S1555CurveInvolution` is the actual `[-1]` involution on the projective
  curve-point group of the concrete punctured elliptic curve;
* it is involutive, nontrivial and fixes the puncture.

`HyperbolicOrbicurve.Hom` is by definition a morphism of the represented
etale stacks (`X.stack.Hom Y.stack`), not a map of curve points.  Therefore the
curve involution does not construct `ellipticInvolution : xF.Hom xF`; the
exact first missing field is the geometric stack lift of the curve involution
to an endomorphism of the S1419 orbicurve.  Consequently `signAction`,
`quotient` and `quotientWitness` cannot be constructed either.

No fake `Hom`, no arbitrary stack morphism, and no Nonempty gate is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1633SignQuotientBasicActual

open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36.OrbicurveFeasibility
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1555EllipticInvolutionActual

variable {l : PrimeGeFive}

/-- Actual curve involution, re-exported. -/
noncomputable def S1633CurveInvolution :
    concretePuncturedCurve.curve.toProjective.Point →+
      concretePuncturedCurve.curve.toProjective.Point :=
  S1555CurveInvolution

theorem S1633CurveInvolution_involutive :
    Function.Involutive (S1633CurveInvolution) :=
  S1555CurveInvolution_involutive

theorem S1633CurveInvolution_nontrivial :
    S1633CurveInvolution pointTwoThree ≠ pointTwoThree :=
  S1555CurveInvolution_nontrivial

theorem S1633CurveInvolution_fixes_puncture :
    S1633CurveInvolution concretePuncturedCurve.puncture =
      concretePuncturedCurve.puncture :=
  S1555CurveInvolution_fixes_puncture

/-- Exact first missing field: a geometric stack endomorphism of the S1419
orbicurve lifting the curve involution. -/
abbrev S1633MissingGeometricInvolution : Type 1 :=
  (S1536XF (l := l)).Hom (S1536XF (l := l))

/-- Exact dependent field: a sign action exists only after the geometric
involution is supplied. -/
abbrev S1633MissingSignAction
    (_h : S1633MissingGeometricInvolution (l := l)) : Type 1 :=
  Iut.OrbicurveSignAction (S1536XF (l := l))

/-- Exact dependent field: the sign-invariant quotient morphism, conditional on
a sign action and the quotient orbicurve. -/
abbrev S1633MissingQuotient
    (signAction : Iut.OrbicurveSignAction (S1536XF (l := l)))
    (cF : Iut.HyperbolicOrbicurve (S1280Arithmetic l).F) : Type 1 :=
  Iut.OrbicurveSignInvariantMorphism signAction cF

/-- Exact dependent field: the sign quotient witness. -/
abbrev S1633MissingQuotientWitness
    {signAction : Iut.OrbicurveSignAction (S1536XF (l := l))}
    {cF : Iut.HyperbolicOrbicurve (S1280Arithmetic l).F}
    (quotient : Iut.OrbicurveSignInvariantMorphism signAction cF) : Type 1 :=
  Iut.OrbicurveSignQuotientWitness signAction quotient

end LeanFormal.IUT.XiFPaper.S1633SignQuotientBasicActual

end
