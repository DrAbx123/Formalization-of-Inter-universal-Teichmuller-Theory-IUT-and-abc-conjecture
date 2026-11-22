import tmp.sheaf.xif.paper.S2857StackAutoForA6Actual
import tmp.sheaf.xif.paper.S2855A6CoreFromD6ConditionalActual

noncomputable section
open LeanFormal.IUT
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2857StackAutoForA6Actual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2856A6CoreWithInvolution

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- A6 geometric core with the D6 stack automorphism as elliptic involution.
The remaining 18 core fields are explicit. -/
noncomputable def S2856Core
    (α : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X)
    (hα : α ≫ α = 𝟙 S2844D6F6BaseChangeActual.S2844X)
    (unique_elliptic_involution :
      ∀ inv : S2855HyperbolicOrbicurve.Hom S2855HyperbolicOrbicurve,
        Iut.HyperbolicOrbicurve.Hom.TwoIso
          (Iut.HyperbolicOrbicurve.Hom.comp inv inv)
          (Iut.HyperbolicOrbicurve.Hom.id S2855HyperbolicOrbicurve) →
        inv = S2857StackAuto α)
    (signAction : Iut.OrbicurveSignAction S2855HyperbolicOrbicurve)
    (signAction_inversion_eq_ellipticInvolution :
      signAction.inversion = S2857StackAuto α)
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
    SourceSignQuotientGeometricCore S2847A6 :=
  S2855Core
    (S2857StackAuto α)
    (S2857StackAuto_square α hα)
    unique_elliptic_involution signAction
    signAction_inversion_eq_ellipticInvolution cF quotient quotientWitness
    xFGroups cFGroups fGroupInclusion xK cK xKExtension cKExtension
    xKType cKType xK_eq_extension cK_eq_extension epsilon

#check S2856Core
#print axioms S2856Core

end LeanFormal.IUT.XiFPaper.S2856A6CoreWithInvolution
end
