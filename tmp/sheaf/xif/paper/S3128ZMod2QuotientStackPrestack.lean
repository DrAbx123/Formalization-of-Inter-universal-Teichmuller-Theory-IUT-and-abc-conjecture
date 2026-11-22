import tmp.sheaf.xif.paper.S1997LTorsRootStackActual
import tmp.sheaf.xif.paper.S2002RootStackificationActual
import Iut.Foundations.Orbicurve
import tmp.sheaf.xif.paper.S1742TwoYonedaActual
noncomputable section
open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1997LTorsRootStackActual
open LeanFormal.IUT.XiFPaper.S2002RootStackificationActual
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3128ZMod2QuotientStackPrestack
universe u

/-! ## Reusable structures / API

From S1997:
* `S1997RootObj R l` = `{b : R // b^l = 0}`
* `S1997RootHom R l x y` = unit `zeta` with `zeta^l = 1` and `y.b = zeta*x.b`
* `S1997RootCategory R l`
* `S1997RootPrestack K l : Pseudofunctor (LocallyDiscrete (SchemeOverField K)ᵒᵖ) Cat`
* `S1997RootEffectiveDescent K l : Prop`

From S2002:
* `isStack_of_isPrestack_and_essSurj`
* `S2002LocalRootDatum U`
* `S1997RootStackification K l` = `{stack, isStack, comparison, origin_faithful}`
* `S2002RootStackificationDatum`
* groupoid instance `S2002RootGroupoid`

Object fields of the `[Z/mu_l]` model:
* torsor/cover `P` over the test object;
* sign action on `X`;
* equivariant stack morphism `P → X`;
* cocycle/invariance data for the sign action.
-/

#check S1997RootObj
#check S1997RootHom
#check S1997RootCategory
#check S1997RootPrestack
#check S1997RootEffectiveDescent
#check isStack_of_isPrestack_and_essSurj
#check S2002LocalRootDatum
#check S1997RootStackification

/-- Shape of a Z/2 quotient-prestack object over a test scheme `U`:
`(Z/2-torsor P, SignGroup-equivariant map P → X)`. -/
structure S3128ZMod2PrestackObject
    {F : Type} [Field F]
    (X : HyperbolicOrbicurve F) (U : SchemeOverField F) where
  /-- The Z/2-torsor total scheme over `U` (chosen explicitly). -/
  P : SchemeOverField F
  /-- The Z/2 action on the underlying scheme. -/
  zmod2_action : MulAction (ZMod 2) P.left
  /-- Simply transitive (torsor) property. -/
  torsor : ∀ p q : P.left, ∃! g : ZMod 2, g • p = q
  /-- The sign action on the target orbicurve. -/
  signAction : OrbicurveSignAction X
  /-- The map `P → X` as a stack morphism (chosen explicitly). -/
  stackMap : Pseudofunctor.StrongTrans
    (LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual.S1742YS P) X.stack.fiber
  /-- Explicit equivariance datum (shape only; the actual cocycle is a
  further input, not fabricated here). -/
  equivariantData : Prop
  equivariantData_proof : equivariantData

#check S3128ZMod2PrestackObject

structure S3128QuotientWitnessData
    {F : Type} [Field F]
    {X C : HyperbolicOrbicurve F}
    (action : OrbicurveSignAction X)
    (quotient : OrbicurveSignInvariantMorphism action C) where
  descend :
    ∀ (Y : HyperbolicOrbicurve F),
      OrbicurveSignInvariantMorphism action Y → C.Hom Y
  factor :
    ∀ (Y : HyperbolicOrbicurve F)
      (invariant : OrbicurveSignInvariantMorphism action Y),
      HyperbolicOrbicurve.Hom.TwoIso
        (HyperbolicOrbicurve.Hom.comp quotient.map (descend Y invariant))
        invariant.map
  descendTwoCell :
    ∀ (Y : HyperbolicOrbicurve F)
      (source target : OrbicurveSignInvariantMorphism action Y),
      OrbicurveSignInvariantMorphism.Hom source target →
        HyperbolicOrbicurve.Hom.TwoCell (descend Y source) (descend Y target)
  descendTwoCell_factor :
    ∀ (Y : HyperbolicOrbicurve F)
      (source target : OrbicurveSignInvariantMorphism action Y)
      (alpha : OrbicurveSignInvariantMorphism.Hom source target),
      Pseudofunctor.StrongTrans.whiskerLeft quotient.map
          (descendTwoCell Y source target alpha) =
        (factor Y source).hom ≫ alpha.app ≫ (factor Y target).inv
  twoCell_ext :
    ∀ (Y : HyperbolicOrbicurve F)
      {first second : C.Hom Y}
      (alpha beta : HyperbolicOrbicurve.Hom.TwoCell first second),
      Pseudofunctor.StrongTrans.whiskerLeft quotient.map alpha =
        Pseudofunctor.StrongTrans.whiskerLeft quotient.map beta →
          alpha = beta

noncomputable def S3128OrbicurveSignQuotientWitness
    {F : Type} [Field F]
    {X C : HyperbolicOrbicurve F}
    {action : OrbicurveSignAction X}
    {quotient : OrbicurveSignInvariantMorphism action C}
    (D : S3128QuotientWitnessData action quotient) :
    OrbicurveSignQuotientWitness action quotient where
  descend := D.descend
  factor := D.factor
  descendTwoCell := D.descendTwoCell
  descendTwoCell_factor := D.descendTwoCell_factor
  twoCell_ext := D.twoCell_ext

#check S3128QuotientWitnessData
#check S3128OrbicurveSignQuotientWitness

end LeanFormal.IUT.XiFPaper.S3128ZMod2QuotientStackPrestack