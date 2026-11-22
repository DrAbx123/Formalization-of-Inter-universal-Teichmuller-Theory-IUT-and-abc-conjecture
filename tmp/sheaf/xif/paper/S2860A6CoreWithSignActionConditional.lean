import tmp.sheaf.xif.paper.S2858A6SFromCore
import tmp.sheaf.xif.paper.S2852OrbicurveSignActionCoherentActual
import tmp.sheaf.xif.paper.S2857StackAutoForA6Actual
import tmp.sheaf.xif.paper.S2847A6ArithmeticActual
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2858A6SFromCore
open LeanFormal.IUT.XiFPaper.S2857StackAutoForA6Actual
open LeanFormal.IUT.XiFPaper.S2856A6CoreWithInvolution
open LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2860A6CoreWithSignActionConditional

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance : Field S2847A6.F := S2847A6.fieldF
local instance : NumberField S2847A6.F := S2847A6.numberFieldF

/-- The 16 remaining geometric-core fields, after signAction and its inversion
equation are filled from S2852 + S2857. -/
structure S2860CoreInputs
    (α : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X)
    (hα : α ≫ α = 𝟙 S2844D6F6BaseChangeActual.S2844X)
    (D : Pseudofunctor Iut.SignActionIndex
      (Iut.EtaleStackPseudofunctor S2847A6.F))
    (atBase : Bicategory.Equivalence (D.obj Iut.signActionObject)
      S2855HyperbolicOrbicurve.stack.fiber)
    (generator_identification :
      (atBase.inv ≫ D.map Iut.signActionGenerator) ≫ atBase.hom ≅
        S2857StackAuto α) where
  unique_elliptic_involution :
    ∀ inv : S2855HyperbolicOrbicurve.Hom S2855HyperbolicOrbicurve,
      Iut.HyperbolicOrbicurve.Hom.TwoIso
        (Iut.HyperbolicOrbicurve.Hom.comp inv inv)
        (Iut.HyperbolicOrbicurve.Hom.id S2855HyperbolicOrbicurve) →
      inv = S2857StackAuto α
  cF : Iut.HyperbolicOrbicurve S2847A6.F
  quotient : Iut.OrbicurveSignInvariantMorphism
    (Iut.orbicurveSignActionOf S2855HyperbolicOrbicurve D atBase
      (S2857StackAuto α) generator_identification
      (S2857StackAuto_square α hα)) cF
  quotientWitness : Iut.OrbicurveSignQuotientWitness
    (Iut.orbicurveSignActionOf S2855HyperbolicOrbicurve D atBase
      (S2857StackAuto α) generator_identification
      (S2857StackAuto_square α hα)) quotient
  xFGroups : SourceOrbicurveGroupData S2855HyperbolicOrbicurve
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
    S2855HyperbolicOrbicurve
  cKExtension : SourceOrbicurveScalarExtension S2847A6.F S2847A6.K cF
  xKType : xK.signature = sourceTypeOneLTorsion S2771FiveLabel
  cKType : cK.signature = sourceTypeOneLTorsionPlusMinus S2771FiveLabel
  xK_eq_extension : xK = xKExtension.result
  cK_eq_extension : cK = cKExtension.result
  epsilon : Iut.OrbicurveBoundaryCusp cK

/-- S for A6 with signAction filled from S2852 and S2857. -/
noncomputable def S2860S
    (α : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X)
    (hα : α ≫ α = 𝟙 S2844D6F6BaseChangeActual.S2844X)
    (D : Pseudofunctor Iut.SignActionIndex
      (Iut.EtaleStackPseudofunctor S2847A6.F))
    (atBase : Bicategory.Equivalence (D.obj Iut.signActionObject)
      S2855HyperbolicOrbicurve.stack.fiber)
    (generator_identification :
      (atBase.inv ≫ D.map Iut.signActionGenerator) ≫ atBase.hom ≅
        S2857StackAuto α)
    (I : S2860CoreInputs α hα D atBase generator_identification) :
    SourceSignQuotientData S2847A6 :=
  S2858S α hα
    { unique_elliptic_involution := I.unique_elliptic_involution
      signAction := Iut.orbicurveSignActionOf S2855HyperbolicOrbicurve D atBase
        (S2857StackAuto α) generator_identification
        (S2857StackAuto_square α hα)
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

/-- A6 completion with S2860S as S. -/
noncomputable def S2860Completion
    (α : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X)
    (hα : α ≫ α = 𝟙 S2844D6F6BaseChangeActual.S2844X)
    (D : Pseudofunctor Iut.SignActionIndex
      (Iut.EtaleStackPseudofunctor S2847A6.F))
    (atBase : Bicategory.Equivalence (D.obj Iut.signActionObject)
      S2855HyperbolicOrbicurve.stack.fiber)
    (generator_identification :
      (atBase.inv ≫ D.map Iut.signActionGenerator) ≫ atBase.hom ≅
        S2857StackAuto α)
    (I : S2860CoreInputs α hα D atBase generator_identification)
    (J : S2858CompletionInputs (S2860S α hα D atBase generator_identification I)) :
    SourceCompletion S2771FiveLabel :=
  S2858Completion α hα _ J

#check S2860S
#check S2860Completion
#print axioms S2860S
#print axioms S2860Completion

end LeanFormal.IUT.XiFPaper.S2860A6CoreWithSignActionConditional
end
