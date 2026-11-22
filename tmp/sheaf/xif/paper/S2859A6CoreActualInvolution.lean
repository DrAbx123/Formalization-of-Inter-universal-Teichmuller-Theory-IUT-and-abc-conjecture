import tmp.sheaf.xif.paper.S2858AlphaOverActual
import tmp.sheaf.xif.paper.S2856A6CoreWithInvolution
import tmp.sheaf.xif.paper.S2858A6SFromCore
import tmp.sheaf.xif.paper.S2841A6PlaceSelectionActual
import tmp.sheaf.xif.paper.S2848A6CompletionConditionalActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2858AlphaOverActual
open LeanFormal.IUT.XiFPaper.S2856A6CoreWithInvolution
open LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual
open LeanFormal.IUT.XiFPaper.S2857StackAutoForA6Actual
open LeanFormal.IUT.XiFPaper.S2858A6SFromCore
open LeanFormal.IUT.XiFPaper.S2841A6PlaceSelectionActual
open LeanFormal.IUT.XiFPaper.S2848A6CompletionConditionalActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open CategoryTheory
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2859A6CoreActualInvolution

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance : Field S2847A6.F := S2847A6.fieldF
local instance : NumberField S2847A6.F := S2847A6.numberFieldF

/-- The 18 remaining core fields after the actual involution alphaOverS2844 and
its square are filled. -/
structure S2859CoreInputs where
  unique_elliptic_involution :
    ∀ inv : LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve.Hom
        LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve,
      Iut.HyperbolicOrbicurve.Hom.TwoIso
        (Iut.HyperbolicOrbicurve.Hom.comp inv inv)
        (Iut.HyperbolicOrbicurve.Hom.id
          LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve) →
      inv = S2857StackAuto alphaOverS2844
  signAction : Iut.OrbicurveSignAction
    LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve
  signAction_inversion_eq_ellipticInvolution :
    signAction.inversion = S2857StackAuto alphaOverS2844
  cF : Iut.HyperbolicOrbicurve S2847A6.F
  quotient : Iut.OrbicurveSignInvariantMorphism signAction cF
  quotientWitness : Iut.OrbicurveSignQuotientWitness signAction quotient
  xFGroups : SourceOrbicurveGroupData
    LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve
    (Iut.AbsoluteGaloisProfinite S2847A6.F)
  cFGroups : SourceOrbicurveGroupData cF
    (Iut.AbsoluteGaloisProfinite S2847A6.F)
  fGroupInclusion : Iut.ProfiniteFundamentalGroupInclusion
    xFGroups.sequence.geometric xFGroups.sequence.arithmetic
    cFGroups.sequence.geometric cFGroups.sequence.arithmetic
    (Iut.AbsoluteGaloisProfinite S2847A6.F) xFGroups.sequence cFGroups.sequence
  xK : Iut.HyperbolicOrbicurve S2847A6.K
  cK : Iut.HyperbolicOrbicurve S2847A6.K
  xKExtension : SourceOrbicurveScalarExtension S2847A6.F S2847A6.K
    LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve
  cKExtension : SourceOrbicurveScalarExtension S2847A6.F S2847A6.K cF
  xKType : xK.signature = sourceTypeOneLTorsion S2771FiveLabel
  cKType : cK.signature = sourceTypeOneLTorsionPlusMinus S2771FiveLabel
  xK_eq_extension : xK = xKExtension.result
  cK_eq_extension : cK = cKExtension.result
  epsilon : Iut.OrbicurveBoundaryCusp cK

/-- Actual-involution A6 geometric core: alphaOverS2844 is the involution. -/
noncomputable def S2859Core (I : S2859CoreInputs) :
    SourceSignQuotientGeometricCore S2847A6 :=
  S2856Core alphaOverS2844 alphaOverS2844_square
    I.unique_elliptic_involution I.signAction
    I.signAction_inversion_eq_ellipticInvolution I.cF I.quotient
    I.quotientWitness I.xFGroups I.cFGroups I.fGroupInclusion I.xK I.cK
    I.xKExtension I.cKExtension I.xKType I.cKType I.xK_eq_extension
    I.cK_eq_extension I.epsilon

/-- The A6 S from the actual-involution core. -/
noncomputable def S2859S (I : S2859CoreInputs) :
    SourceSignQuotientData S2847A6 :=
  (S2859Core I).toSourceSignQuotientData S2841PlaceSelection

/-- A6 completion with S2859S as S. -/
noncomputable def S2859Completion
    (I : S2859CoreInputs)
    (J : S2858CompletionInputs (S2859S I)) :
    SourceCompletion S2771FiveLabel :=
  S2848Completion (S2859S I) J.multiplicative J.qWitness
    J.residueCoprime J.imageContainsSL2 J.kSide J.localFamily J.boundary

#check S2859Core
#check S2859S
#check S2859Completion
#print axioms S2859Core
#print axioms S2859S
#print axioms S2859Completion

end LeanFormal.IUT.XiFPaper.S2859A6CoreActualInvolution
end
