/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1A2QuotientMorphismActual
import Mathlib.Tactic

/-! # A2 node03: clean producer interface for the sign quotient stack -/
noncomputable section
open CategoryTheory Bicategory
open scoped CategoryTheory.Bicategory
open scoped CategoryTheory.Pseudofunctor.StrongTrans
namespace LeanFormal.IUT.XiFPaper.Mzk1A2Node03QuotientStackProducerActual
open LeanFormal.IUT
open Iut
universe u
variable {F : Type u} [Field F]
variable {X C : Iut.HyperbolicOrbicurve F}
variable (action : Iut.OrbicurveSignAction X)
variable (quotient : Iut.OrbicurveSignInvariantMorphism action C)

/-- Exact producer data for `OrbicurveSignQuotientWitness`: the universal
property fields, to be filled by the actual quotient stack `[U/G]`. -/
structure A2QuotientStackProducerData where
  descend :
    ∀ (Y : Iut.HyperbolicOrbicurve F),
      Iut.OrbicurveSignInvariantMorphism action Y → C.Hom Y
  factor :
    ∀ (Y : Iut.HyperbolicOrbicurve F)
      (invariant : Iut.OrbicurveSignInvariantMorphism action Y),
      Iut.HyperbolicOrbicurve.Hom.TwoIso
        (Iut.HyperbolicOrbicurve.Hom.comp quotient.map (descend Y invariant))
        invariant.map
  descendTwoCell :
    ∀ (Y : Iut.HyperbolicOrbicurve F)
      (source target : Iut.OrbicurveSignInvariantMorphism action Y),
      Iut.OrbicurveSignInvariantMorphism.Hom source target →
        Iut.HyperbolicOrbicurve.Hom.TwoCell (descend Y source) (descend Y target)
  descendTwoCell_factor :
    ∀ (Y : Iut.HyperbolicOrbicurve F)
      (source target : Iut.OrbicurveSignInvariantMorphism action Y)
      (alpha : Iut.OrbicurveSignInvariantMorphism.Hom source target),
      Pseudofunctor.StrongTrans.whiskerLeft quotient.map
          (descendTwoCell Y source target alpha) =
        (factor Y source).hom ≫ alpha.app ≫ (factor Y target).inv
  twoCell_ext :
    ∀ (Y : Iut.HyperbolicOrbicurve F)
      {first second : C.Hom Y}
      (alpha beta : Iut.HyperbolicOrbicurve.Hom.TwoCell first second),
      Pseudofunctor.StrongTrans.whiskerLeft quotient.map alpha =
        Pseudofunctor.StrongTrans.whiskerLeft quotient.map beta → alpha = beta

def A2QuotientStackProducerData.toWitness
    (D : A2QuotientStackProducerData action quotient) :
    Iut.OrbicurveSignQuotientWitness action quotient where
  descend := D.descend
  factor := D.factor
  descendTwoCell := D.descendTwoCell
  descendTwoCell_factor := D.descendTwoCell_factor
  twoCell_ext := D.twoCell_ext

def A2QuotientStackProducerRequired : Prop :=
  Nonempty (A2QuotientStackProducerData action quotient)

end LeanFormal.IUT.XiFPaper.Mzk1A2Node03QuotientStackProducerActual
