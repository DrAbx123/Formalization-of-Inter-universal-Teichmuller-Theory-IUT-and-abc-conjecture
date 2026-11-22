/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1A2Node03QuotientStackProducerActual
import Mathlib.Tactic

/-! # A2 node03: consumer/assembly of the quotient-stack producer data -/
noncomputable section
open CategoryTheory Bicategory
open scoped CategoryTheory.Bicategory
open scoped CategoryTheory.Pseudofunctor.StrongTrans
namespace LeanFormal.IUT.XiFPaper.Mzk1A2Node03QuotientStackConsumerActual
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.Mzk1A2Node03QuotientStackProducerActual
universe u
variable {F : Type u} [Field F]
variable {X C : Iut.HyperbolicOrbicurve F}
variable (action : Iut.OrbicurveSignAction X)
variable (quotient : Iut.OrbicurveSignInvariantMorphism action C)

/-- A2 node03 consumer: the producer data is the only input needed to obtain
the universal property of `C=[X/G]`. -/
structure A2Node03QuotientStackConsumerData where
  producer : A2QuotientStackProducerData action quotient

def A2Node03QuotientStackConsumerData.toWitness
    (D : A2Node03QuotientStackConsumerData action quotient) :
    Iut.OrbicurveSignQuotientWitness action quotient :=
  D.producer.toWitness

theorem A2Node03QuotientStackConsumerData.nonempty_witness
    (D : A2Node03QuotientStackConsumerData action quotient) :
    Nonempty (Iut.OrbicurveSignQuotientWitness action quotient) :=
  ⟨D.toWitness⟩

theorem A2Node03QuotientStackConsumerRequired_iff :
    Nonempty (A2Node03QuotientStackConsumerData action quotient) ↔
      Nonempty (A2QuotientStackProducerData action quotient) := by
  constructor
  · rintro ⟨D⟩; exact ⟨D.producer⟩
  · rintro ⟨P⟩; exact ⟨⟨P⟩⟩

end LeanFormal.IUT.XiFPaper.Mzk1A2Node03QuotientStackConsumerActual
