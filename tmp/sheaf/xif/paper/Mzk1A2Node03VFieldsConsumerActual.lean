/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1A2Node03SourceVFieldsActual
import tmp.sheaf.xif.paper.Mzk1A2Node03SourceWitnessConsumerActual
import Mathlib.Tactic

/-! # A2 node03: connect V/epsilon fields to SourceSignQuotientData -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1A2Node03VFieldsConsumerActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.Mzk1A2Node03SourceVFieldsActual
open LeanFormal.IUT.XiFPaper.Mzk1A2Node03SourceWitnessConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1A2Node03QuotientStackProducerActual

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}

structure A2Node03VFieldsAndProducerData (S : SourceSignQuotientData A) where
  vFields : A2Node03SourceVFieldsData S
  producer : A2QuotientStackProducerData S.signAction S.quotient

noncomputable def sourceSignQuotientDataWithVFieldsAndProducerWitness
    (S : SourceSignQuotientData A)
    (D : A2Node03VFieldsAndProducerData S) :
    SourceSignQuotientData A :=
  sourceSignQuotientDataWithProducerWitness
    (sourceSignQuotientDataWithVFields S D.vFields) D.producer

@[simp] theorem sourceSignQuotientDataWithVFieldsAndProducerWitness_V
    (S : SourceSignQuotientData A)
    (D : A2Node03VFieldsAndProducerData S) :
    (sourceSignQuotientDataWithVFieldsAndProducerWitness S D).V = D.vFields.V := rfl

def A2Node03VFieldsAndProducerRequired
    (S : SourceSignQuotientData A) : Prop :=
  Nonempty (A2Node03VFieldsAndProducerData S)

end LeanFormal.IUT.XiFPaper.Mzk1A2Node03VFieldsConsumerActual
