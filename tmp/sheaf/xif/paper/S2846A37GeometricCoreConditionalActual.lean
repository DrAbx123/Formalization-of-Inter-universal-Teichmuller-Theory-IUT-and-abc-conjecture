import tmp.sheaf.xif.paper.S2837PlaceSelectionArithmetic37Actual
import LeanFormal.IUT.IUTI.InitialTheta.SourceSignQuotientConstruction
import LeanFormal.IUT.IUTI.HodgeTheater.SourceDefinition31SignQuotientSupplyReduction

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2784KernelFieldActual
open LeanFormal.IUT.XiFPaper.S2837PlaceSelectionArithmetic37Actual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2846A37GeometricCoreConditionalActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- Conditional geometric core for arithmetic37, all orbicurve/sign/group/cusp
fields explicit. -/
noncomputable def S2846Core
    (xF : Iut.HyperbolicOrbicurve arithmetic37.F)
    (xF_geometry : SourceOncePuncturedGeometry arithmetic37.curve xF)
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
    (cF : Iut.HyperbolicOrbicurve arithmetic37.F)
    (quotient : Iut.OrbicurveSignInvariantMorphism signAction cF)
    (quotientWitness : Iut.OrbicurveSignQuotientWitness signAction quotient)
    (xFGroups : SourceOrbicurveGroupData xF
      (Iut.AbsoluteGaloisProfinite arithmetic37.F))
    (cFGroups : SourceOrbicurveGroupData cF
      (Iut.AbsoluteGaloisProfinite arithmetic37.F))
    (fGroupInclusion : Iut.ProfiniteFundamentalGroupInclusion
      xFGroups.sequence.geometric xFGroups.sequence.arithmetic
      cFGroups.sequence.geometric cFGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite arithmetic37.F)
      xFGroups.sequence cFGroups.sequence)
    (xK : Iut.HyperbolicOrbicurve arithmetic37.K)
    (cK : Iut.HyperbolicOrbicurve arithmetic37.K)
    (xKExtension : SourceOrbicurveScalarExtension arithmetic37.F arithmetic37.K xF)
    (cKExtension : SourceOrbicurveScalarExtension arithmetic37.F arithmetic37.K cF)
    (xKType : xK.signature = sourceTypeOneLTorsion S2771FiveLabel)
    (cKType : cK.signature = sourceTypeOneLTorsionPlusMinus S2771FiveLabel)
    (xK_eq_extension : xK = xKExtension.result)
    (cK_eq_extension : cK = cKExtension.result)
    (epsilon : Iut.OrbicurveBoundaryCusp cK) :
    SourceSignQuotientGeometricCore arithmetic37 where
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

/-- Full SourceSignQuotientData for arithmetic37 from the conditional geometric
core and the actual S2837 place selection. -/
noncomputable def S2846SignQuotientData
    (xF : Iut.HyperbolicOrbicurve arithmetic37.F)
    (xF_geometry : SourceOncePuncturedGeometry arithmetic37.curve xF)
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
    (cF : Iut.HyperbolicOrbicurve arithmetic37.F)
    (quotient : Iut.OrbicurveSignInvariantMorphism signAction cF)
    (quotientWitness : Iut.OrbicurveSignQuotientWitness signAction quotient)
    (xFGroups : SourceOrbicurveGroupData xF
      (Iut.AbsoluteGaloisProfinite arithmetic37.F))
    (cFGroups : SourceOrbicurveGroupData cF
      (Iut.AbsoluteGaloisProfinite arithmetic37.F))
    (fGroupInclusion : Iut.ProfiniteFundamentalGroupInclusion
      xFGroups.sequence.geometric xFGroups.sequence.arithmetic
      cFGroups.sequence.geometric cFGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite arithmetic37.F)
      xFGroups.sequence cFGroups.sequence)
    (xK : Iut.HyperbolicOrbicurve arithmetic37.K)
    (cK : Iut.HyperbolicOrbicurve arithmetic37.K)
    (xKExtension : SourceOrbicurveScalarExtension arithmetic37.F arithmetic37.K xF)
    (cKExtension : SourceOrbicurveScalarExtension arithmetic37.F arithmetic37.K cF)
    (xKType : xK.signature = sourceTypeOneLTorsion S2771FiveLabel)
    (cKType : cK.signature = sourceTypeOneLTorsionPlusMinus S2771FiveLabel)
    (xK_eq_extension : xK = xKExtension.result)
    (cK_eq_extension : cK = cKExtension.result)
    (epsilon : Iut.OrbicurveBoundaryCusp cK) :
    SourceSignQuotientData arithmetic37 :=
  (S2846Core xF xF_geometry ellipticInvolution ellipticInvolution_squared
    unique_elliptic_involution signAction
    signAction_inversion_eq_ellipticInvolution cF quotient quotientWitness
    xFGroups cFGroups fGroupInclusion xK cK xKExtension cKExtension
    xKType cKType xK_eq_extension cK_eq_extension epsilon).toSourceSignQuotientData
    S2837PlaceSelection

#check S2846Core
#check S2846SignQuotientData
#print axioms S2846Core
#print axioms S2846SignQuotientData

end LeanFormal.IUT.XiFPaper.S2846A37GeometricCoreConditionalActual
end
