import tmp.sheaf.xif.paper.S2859A6CoreActualInvolution
import tmp.sheaf.xif.paper.S2852OrbicurveSignActionCoherentActual
import tmp.sheaf.xif.paper.S2858AlphaOverActual
import tmp.sheaf.xif.paper.S2841A6PlaceSelectionActual
import tmp.sheaf.xif.paper.S2848A6CompletionConditionalActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2859A6CoreActualInvolution
open LeanFormal.IUT.XiFPaper.S2858AlphaOverActual
open LeanFormal.IUT.XiFPaper.S2857StackAutoForA6Actual
open LeanFormal.IUT.XiFPaper.S2841A6PlaceSelectionActual
open LeanFormal.IUT.XiFPaper.S2848A6CompletionConditionalActual
open LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual
open LeanFormal.IUT.XiFPaper.S2858A6SFromCore
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2867A6CoreActualInvolutionSignAction

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2847A6.F := S2847A6.fieldF
local instance : NumberField S2847A6.F := S2847A6.numberFieldF

/-- 16 remaining fields once alphaOverS2844 is the actual involution and
signAction is built from S2852. -/
structure S2867CoreInputs
    (D : Pseudofunctor Iut.SignActionIndex
      (Iut.EtaleStackPseudofunctor S2847A6.F))
    (atBase : Bicategory.Equivalence (D.obj Iut.signActionObject)
      LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve.stack.fiber)
    (generator_identification :
      (atBase.inv ≫ D.map Iut.signActionGenerator) ≫ atBase.hom ≅
        S2857StackAuto alphaOverS2844) where
  unique_elliptic_involution :
    ∀ inv : LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve.Hom
        LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve,
      Iut.HyperbolicOrbicurve.Hom.TwoIso
        (Iut.HyperbolicOrbicurve.Hom.comp inv inv)
        (Iut.HyperbolicOrbicurve.Hom.id
          LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve) →
      inv = S2857StackAuto alphaOverS2844
  cF : Iut.HyperbolicOrbicurve S2847A6.F
  quotient : Iut.OrbicurveSignInvariantMorphism
    (Iut.orbicurveSignActionOf
      LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve
      D atBase (S2857StackAuto alphaOverS2844) generator_identification
      (S2857StackAuto_square alphaOverS2844 alphaOverS2844_square)) cF
  quotientWitness : Iut.OrbicurveSignQuotientWitness
    (Iut.orbicurveSignActionOf
      LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve
      D atBase (S2857StackAuto alphaOverS2844) generator_identification
      (S2857StackAuto_square alphaOverS2844 alphaOverS2844_square)) quotient
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

/-- A6 core with actual involution and explicit-D signAction. -/
noncomputable def S2867Core
    (D : Pseudofunctor Iut.SignActionIndex
      (Iut.EtaleStackPseudofunctor S2847A6.F))
    (atBase : Bicategory.Equivalence (D.obj Iut.signActionObject)
      LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve.stack.fiber)
    (generator_identification :
      (atBase.inv ≫ D.map Iut.signActionGenerator) ≫ atBase.hom ≅
        S2857StackAuto alphaOverS2844)
    (I : S2867CoreInputs D atBase generator_identification) :
    SourceSignQuotientGeometricCore S2847A6 :=
  S2859Core
    { unique_elliptic_involution := I.unique_elliptic_involution
      signAction := Iut.orbicurveSignActionOf
        LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve
        D atBase (S2857StackAuto alphaOverS2844) generator_identification
        (S2857StackAuto_square alphaOverS2844 alphaOverS2844_square)
      signAction_inversion_eq_ellipticInvolution := rfl
      cF := I.cF
      quotient := I.quotient
      quotientWitness := I.quotientWitness
      xFGroups := I.xFGroups
      cFGroups := I.cFGroups
      fGroupInclusion := I.fGroupInclusion
      xK := I.xK
      cK := I.cK
      xKExtension := I.xKExtension
      cKExtension := I.cKExtension
      xKType := I.xKType
      cKType := I.cKType
      xK_eq_extension := I.xK_eq_extension
      cK_eq_extension := I.cK_eq_extension
      epsilon := I.epsilon }

/-- A6 S with actual involution and explicit-D signAction. -/
noncomputable def S2867S
    (D : Pseudofunctor Iut.SignActionIndex
      (Iut.EtaleStackPseudofunctor S2847A6.F))
    (atBase : Bicategory.Equivalence (D.obj Iut.signActionObject)
      LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve.stack.fiber)
    (generator_identification :
      (atBase.inv ≫ D.map Iut.signActionGenerator) ≫ atBase.hom ≅
        S2857StackAuto alphaOverS2844)
    (I : S2867CoreInputs D atBase generator_identification) :
    SourceSignQuotientData S2847A6 :=
  (S2867Core D atBase generator_identification I).toSourceSignQuotientData
    S2841PlaceSelection

/-- A6 completion with S2867S. -/
noncomputable def S2867Completion
    (D : Pseudofunctor Iut.SignActionIndex
      (Iut.EtaleStackPseudofunctor S2847A6.F))
    (atBase : Bicategory.Equivalence (D.obj Iut.signActionObject)
      LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve.stack.fiber)
    (generator_identification :
      (atBase.inv ≫ D.map Iut.signActionGenerator) ≫ atBase.hom ≅
        S2857StackAuto alphaOverS2844)
    (I : S2867CoreInputs D atBase generator_identification)
    (J : S2858CompletionInputs (S2867S D atBase generator_identification I)) :
    SourceCompletion S2771FiveLabel :=
  S2848Completion (S2867S D atBase generator_identification I)
    J.multiplicative J.qWitness J.residueCoprime J.imageContainsSL2
    J.kSide J.localFamily J.boundary

#check S2867Core
#check S2867S
#check S2867Completion
#print axioms S2867Core
#print axioms S2867S
#print axioms S2867Completion

end LeanFormal.IUT.XiFPaper.S2867A6CoreActualInvolutionSignAction
end
