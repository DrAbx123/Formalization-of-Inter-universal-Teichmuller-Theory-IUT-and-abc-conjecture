import tmp.sheaf.xif.paper.S2867A6CoreActualInvolutionSignAction
import tmp.sheaf.xif.paper.S2854SignQuotientAudit
import tmp.sheaf.xif.paper.S2841A6PlaceSelectionActual
import tmp.sheaf.xif.paper.S2848A6CompletionConditionalActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2867A6CoreActualInvolutionSignAction
open LeanFormal.IUT.XiFPaper.S2854SignQuotientAudit
open LeanFormal.IUT.XiFPaper.S2841A6PlaceSelectionActual
open LeanFormal.IUT.XiFPaper.S2848A6CompletionConditionalActual
open LeanFormal.IUT.XiFPaper.S2858AlphaOverActual
open LeanFormal.IUT.XiFPaper.S2857StackAutoForA6Actual
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

namespace LeanFormal.IUT.XiFPaper.S2869A6CoreWithGenericQuotient

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2847A6.F := S2847A6.fieldF
local instance : NumberField S2847A6.F := S2847A6.numberFieldF

/-- The sign action used in S2867. -/
noncomputable def S2869SignAction
    (D : Pseudofunctor Iut.SignActionIndex
      (Iut.EtaleStackPseudofunctor S2847A6.F))
    (atBase : Bicategory.Equivalence (D.obj Iut.signActionObject)
      LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve.stack.fiber)
    (generator_identification :
      (atBase.inv ≫ D.map Iut.signActionGenerator) ≫ atBase.hom ≅
        S2857StackAuto alphaOverS2844) :
    Iut.OrbicurveSignAction
      LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve :=
  Iut.orbicurveSignActionOf
    LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve
    D atBase (S2857StackAuto alphaOverS2844) generator_identification
    (S2857StackAuto_square alphaOverS2844 alphaOverS2844_square)

/-- 13 remaining fields once a generic stack-quotient witness supplies
cF/quotient/quotientWitness. -/
structure S2869CoreInputs
    (D : Pseudofunctor Iut.SignActionIndex
      (Iut.EtaleStackPseudofunctor S2847A6.F))
    (atBase : Bicategory.Equivalence (D.obj Iut.signActionObject)
      LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve.stack.fiber)
    (generator_identification :
      (atBase.inv ≫ D.map Iut.signActionGenerator) ≫ atBase.hom ≅
        S2857StackAuto alphaOverS2844)
    (W : S2854StackQuotientInput
      LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve
      (S2869SignAction D atBase generator_identification)) where
  unique_elliptic_involution :
    ∀ inv : LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve.Hom
        LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve,
      Iut.HyperbolicOrbicurve.Hom.TwoIso
        (Iut.HyperbolicOrbicurve.Hom.comp inv inv)
        (Iut.HyperbolicOrbicurve.Hom.id
          LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve) →
      inv = S2857StackAuto alphaOverS2844
  xFGroups : SourceOrbicurveGroupData
    LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve
    (Iut.AbsoluteGaloisProfinite S2847A6.F)
  cFGroups : SourceOrbicurveGroupData W.cF
    (Iut.AbsoluteGaloisProfinite S2847A6.F)
  fGroupInclusion : Iut.ProfiniteFundamentalGroupInclusion
    xFGroups.sequence.geometric xFGroups.sequence.arithmetic
    cFGroups.sequence.geometric cFGroups.sequence.arithmetic
    (Iut.AbsoluteGaloisProfinite S2847A6.F) xFGroups.sequence cFGroups.sequence
  xK : Iut.HyperbolicOrbicurve S2847A6.K
  cK : Iut.HyperbolicOrbicurve S2847A6.K
  xKExtension : SourceOrbicurveScalarExtension S2847A6.F S2847A6.K
    LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve
  cKExtension : SourceOrbicurveScalarExtension S2847A6.F S2847A6.K W.cF
  xKType : xK.signature = sourceTypeOneLTorsion S2771FiveLabel
  cKType : cK.signature = sourceTypeOneLTorsionPlusMinus S2771FiveLabel
  xK_eq_extension : xK = xKExtension.result
  cK_eq_extension : cK = cKExtension.result
  epsilon : Iut.OrbicurveBoundaryCusp cK

/-- Actual reduction: a generic stack-quotient witness fills cF/quotient/witness,
leaving 13 fields. -/
noncomputable def S2869Core
    (D : Pseudofunctor Iut.SignActionIndex
      (Iut.EtaleStackPseudofunctor S2847A6.F))
    (atBase : Bicategory.Equivalence (D.obj Iut.signActionObject)
      LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve.stack.fiber)
    (generator_identification :
      (atBase.inv ≫ D.map Iut.signActionGenerator) ≫ atBase.hom ≅
        S2857StackAuto alphaOverS2844)
    (W : S2854StackQuotientInput
      LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve
      (S2869SignAction D atBase generator_identification))
    (I : S2869CoreInputs D atBase generator_identification W) :
    SourceSignQuotientGeometricCore S2847A6 :=
  S2867Core D atBase generator_identification
    { unique_elliptic_involution := I.unique_elliptic_involution
      cF := W.cF
      quotient := W.quotient
      quotientWitness := W.quotientWitness
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

/-- The corresponding S. -/
noncomputable def S2869S
    (D : Pseudofunctor Iut.SignActionIndex
      (Iut.EtaleStackPseudofunctor S2847A6.F))
    (atBase : Bicategory.Equivalence (D.obj Iut.signActionObject)
      LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve.stack.fiber)
    (generator_identification :
      (atBase.inv ≫ D.map Iut.signActionGenerator) ≫ atBase.hom ≅
        S2857StackAuto alphaOverS2844)
    (W : S2854StackQuotientInput
      LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve
      (S2869SignAction D atBase generator_identification))
    (I : S2869CoreInputs D atBase generator_identification W) :
    SourceSignQuotientData S2847A6 :=
  (S2869Core D atBase generator_identification W I).toSourceSignQuotientData
    S2841PlaceSelection

/-- Completion with S2869S. -/
noncomputable def S2869Completion
    (D : Pseudofunctor Iut.SignActionIndex
      (Iut.EtaleStackPseudofunctor S2847A6.F))
    (atBase : Bicategory.Equivalence (D.obj Iut.signActionObject)
      LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve.stack.fiber)
    (generator_identification :
      (atBase.inv ≫ D.map Iut.signActionGenerator) ≫ atBase.hom ≅
        S2857StackAuto alphaOverS2844)
    (W : S2854StackQuotientInput
      LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual.S2855HyperbolicOrbicurve
      (S2869SignAction D atBase generator_identification))
    (I : S2869CoreInputs D atBase generator_identification W)
    (J : S2858CompletionInputs (S2869S D atBase generator_identification W I)) :
    SourceCompletion S2771FiveLabel :=
  S2848Completion (S2869S D atBase generator_identification W I)
    J.multiplicative J.qWitness J.residueCoprime J.imageContainsSL2
    J.kSide J.localFamily J.boundary

#check S2869SignAction
#check S2869Core
#check S2869S
#check S2869Completion
#print axioms S2869Core
#print axioms S2869S
#print axioms S2869Completion

end LeanFormal.IUT.XiFPaper.S2869A6CoreWithGenericQuotient
end
