import tmp.sheaf.xif.paper.S2841A6PlaceSelectionActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceSignQuotientConstruction
import LeanFormal.IUT.IUTI.HodgeTheater.SourceDefinition31SignQuotientSupplyReduction

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2841A6PlaceSelectionActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2850A6SignQuotientConditionalActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- Conditional geometric core for A6. -/
noncomputable def S2850Core
    (xF : Iut.HyperbolicOrbicurve S2847A6.F)
    (xF_geometry : SourceOncePuncturedGeometry S2847A6.curve xF)
    (ellipticInvolution : xF.Hom xF)
    (ellipticInvolution_squared :
      Iut.HyperbolicOrbicurve.Hom.TwoIso
        (Iut.HyperbolicOrbicurve.Hom.comp ellipticInvolution ellipticInvolution)
        (Iut.HyperbolicOrbicurve.Hom.id xF))
    (unique_elliptic_involution :
      ∀ inv : xF.Hom xF,
        Iut.HyperbolicOrbicurve.Hom.TwoIso
          (Iut.HyperbolicOrbicurve.Hom.comp inv inv)
          (Iut.HyperbolicOrbicurve.Hom.id xF) →
        inv = ellipticInvolution)
    (signAction : Iut.OrbicurveSignAction xF)
    (signAction_inversion_eq_ellipticInvolution :
      signAction.inversion = ellipticInvolution)
    (cF : Iut.HyperbolicOrbicurve S2847A6.F)
    (quotient : Iut.OrbicurveSignInvariantMorphism signAction cF)
    (quotientWitness : Iut.OrbicurveSignQuotientWitness signAction quotient)
    (xFGroups : SourceOrbicurveGroupData xF
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
    (xKExtension : SourceOrbicurveScalarExtension S2847A6.F S2847A6.K xF)
    (cKExtension : SourceOrbicurveScalarExtension S2847A6.F S2847A6.K cF)
    (xKType : xK.signature = sourceTypeOneLTorsion S2771FiveLabel)
    (cKType : cK.signature = sourceTypeOneLTorsionPlusMinus S2771FiveLabel)
    (xK_eq_extension : xK = xKExtension.result)
    (cK_eq_extension : cK = cKExtension.result)
    (epsilon : Iut.OrbicurveBoundaryCusp cK) :
    SourceSignQuotientGeometricCore S2847A6 where
  xF := xF
  xF_geometry := xF_geometry
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

noncomputable def S2850SignQuotientData
    (xF : Iut.HyperbolicOrbicurve S2847A6.F)
    (xF_geometry : SourceOncePuncturedGeometry S2847A6.curve xF)
    (ellipticInvolution : xF.Hom xF)
    (ellipticInvolution_squared :
      Iut.HyperbolicOrbicurve.Hom.TwoIso
        (Iut.HyperbolicOrbicurve.Hom.comp ellipticInvolution ellipticInvolution)
        (Iut.HyperbolicOrbicurve.Hom.id xF))
    (unique_elliptic_involution :
      ∀ inv : xF.Hom xF,
        Iut.HyperbolicOrbicurve.Hom.TwoIso
          (Iut.HyperbolicOrbicurve.Hom.comp inv inv)
          (Iut.HyperbolicOrbicurve.Hom.id xF) →
        inv = ellipticInvolution)
    (signAction : Iut.OrbicurveSignAction xF)
    (signAction_inversion_eq_ellipticInvolution :
      signAction.inversion = ellipticInvolution)
    (cF : Iut.HyperbolicOrbicurve S2847A6.F)
    (quotient : Iut.OrbicurveSignInvariantMorphism signAction cF)
    (quotientWitness : Iut.OrbicurveSignQuotientWitness signAction quotient)
    (xFGroups : SourceOrbicurveGroupData xF
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
    (xKExtension : SourceOrbicurveScalarExtension S2847A6.F S2847A6.K xF)
    (cKExtension : SourceOrbicurveScalarExtension S2847A6.F S2847A6.K cF)
    (xKType : xK.signature = sourceTypeOneLTorsion S2771FiveLabel)
    (cKType : cK.signature = sourceTypeOneLTorsionPlusMinus S2771FiveLabel)
    (xK_eq_extension : xK = xKExtension.result)
    (cK_eq_extension : cK = cKExtension.result)
    (epsilon : Iut.OrbicurveBoundaryCusp cK) :
    SourceSignQuotientData S2847A6 :=
  (S2850Core xF xF_geometry ellipticInvolution ellipticInvolution_squared
    unique_elliptic_involution signAction
    signAction_inversion_eq_ellipticInvolution cF quotient quotientWitness
    xFGroups cFGroups fGroupInclusion xK cK xKExtension cKExtension
    xKType cKType xK_eq_extension cK_eq_extension epsilon).toSourceSignQuotientData
    S2841PlaceSelection

#check S2850Core
#check S2850SignQuotientData
#print axioms S2850SignQuotientData

end LeanFormal.IUT.XiFPaper.S2850A6SignQuotientConditionalActual
end
