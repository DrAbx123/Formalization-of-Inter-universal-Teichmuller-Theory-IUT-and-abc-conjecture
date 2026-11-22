import tmp.sheaf.xif.paper.S2851A6D6GeometryActual
import tmp.sheaf.xif.paper.S2848D6F6CompleteActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceSignQuotientConstruction
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2851A6D6GeometryActual
open LeanFormal.IUT.XiFPaper.S2848D6F6CompleteActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.OrbicurveFeasibility
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- The A6 hyperbolic orbicurve, retyped directly over A6.F from S2848D6. -/
noncomputable def S2855HyperbolicOrbicurve :
    Iut.HyperbolicOrbicurve S2847A6.F :=
  realizedHyperbolicOrbicurve S2847A6.F S2848D6.fiber S2848D6.isStack
    Iut.OrbicurveSignature.oncePuncturedElliptic
    Iut.OrbicurveSignature.oncePuncturedElliptic_isHyperbolic

/-- The once-punctured geometry of the A6 curve, with the actual S2851 orbicurve. -/
noncomputable def S2855Geometry :
    SourceOncePuncturedGeometry S2847A6.curve S2855HyperbolicOrbicurve where
  signature := by
    rw [show S2855HyperbolicOrbicurve.signature =
      Iut.OrbicurveSignature.oncePuncturedElliptic by rfl]
    exact oncePuncturedElliptic_eq_sourceTypeOneOne.symm

/-- Conditional SourceSignQuotientGeometricCore for A6: xF and its
once-punctured geometry are actual from S2851; the other 20 fields remain
explicit. -/
noncomputable def S2855Core
    (ellipticInvolution : S2855HyperbolicOrbicurve.Hom S2855HyperbolicOrbicurve)
    (ellipticInvolution_squared :
      Iut.HyperbolicOrbicurve.Hom.TwoIso
        (Iut.HyperbolicOrbicurve.Hom.comp ellipticInvolution ellipticInvolution)
        (Iut.HyperbolicOrbicurve.Hom.id S2855HyperbolicOrbicurve))
    (unique_elliptic_involution :
      ∀ inv : S2855HyperbolicOrbicurve.Hom S2855HyperbolicOrbicurve,
        Iut.HyperbolicOrbicurve.Hom.TwoIso
          (Iut.HyperbolicOrbicurve.Hom.comp inv inv)
          (Iut.HyperbolicOrbicurve.Hom.id S2855HyperbolicOrbicurve) →
        inv = ellipticInvolution)
    (signAction : Iut.OrbicurveSignAction S2855HyperbolicOrbicurve)
    (signAction_inversion_eq_ellipticInvolution :
      signAction.inversion = ellipticInvolution)
    (cF : Iut.HyperbolicOrbicurve S2847A6.F)
    (quotient : Iut.OrbicurveSignInvariantMorphism signAction cF)
    (quotientWitness : Iut.OrbicurveSignQuotientWitness signAction quotient)
    (xFGroups : SourceOrbicurveGroupData S2855HyperbolicOrbicurve
      (Iut.AbsoluteGaloisProfinite S2847A6.F))
    (cFGroups : SourceOrbicurveGroupData cF
      (Iut.AbsoluteGaloisProfinite S2847A6.F))
    (fGroupInclusion : Iut.ProfiniteFundamentalGroupInclusion
      xFGroups.sequence.geometric xFGroups.sequence.arithmetic
      cFGroups.sequence.geometric cFGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite S2847A6.F)
      xFGroups.sequence cFGroups.sequence)
    (xK : Iut.HyperbolicOrbicurve S2847A6.K)
    (cK : Iut.HyperbolicOrbicurve S2847A6.K)
    (xKExtension : SourceOrbicurveScalarExtension S2847A6.F S2847A6.K
      S2855HyperbolicOrbicurve)
    (cKExtension : SourceOrbicurveScalarExtension S2847A6.F S2847A6.K cF)
    (xKType : xK.signature = sourceTypeOneLTorsion S2771FiveLabel)
    (cKType : cK.signature = sourceTypeOneLTorsionPlusMinus S2771FiveLabel)
    (xK_eq_extension : xK = xKExtension.result)
    (cK_eq_extension : cK = cKExtension.result)
    (epsilon : Iut.OrbicurveBoundaryCusp cK) :
    SourceSignQuotientGeometricCore S2847A6 where
  xF := S2855HyperbolicOrbicurve
  xF_geometry := S2855Geometry
  ellipticInvolution := ellipticInvolution
  ellipticInvolution_squared := ellipticInvolution_squared
  unique_elliptic_involution := unique_elliptic_involution
  signAction := signAction
  signAction_inversion_eq_ellipticInvolution :=
    signAction_inversion_eq_ellipticInvolution
  cF := cF
  quotient := quotient
  quotientWitness := quotientWitness
  xFGroups := xFGroups
  cFGroups := cFGroups
  fGroupInclusion := fGroupInclusion
  xK := xK
  cK := cK
  xKExtension := xKExtension
  cKExtension := cKExtension
  xKType := xKType
  cKType := cKType
  xK_eq_extension := xK_eq_extension
  cK_eq_extension := cK_eq_extension
  epsilon := epsilon

#check S2855Core
#print axioms S2855Core

end LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual
end
