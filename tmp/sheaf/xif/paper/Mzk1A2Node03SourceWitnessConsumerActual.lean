/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1A2Node03QuotientStackConsumerActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import Mathlib.Tactic

/-! # A2 node03: connect producer witness to SourceSignQuotientData.quotientWitness -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1A2Node03SourceWitnessConsumerActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.Mzk1A2Node03QuotientStackProducerActual
open LeanFormal.IUT.XiFPaper.Mzk1A2Node03QuotientStackConsumerActual

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}

noncomputable def sourceSignQuotientDataWithProducerWitness
    (S : SourceSignQuotientData A)
    (P : A2QuotientStackProducerData S.signAction S.quotient) :
    SourceSignQuotientData A :=
  { S with quotientWitness := P.toWitness }

@[simp] theorem sourceSignQuotientDataWithProducerWitness_quotientWitness
    (S : SourceSignQuotientData A)
    (P : A2QuotientStackProducerData S.signAction S.quotient) :
    (sourceSignQuotientDataWithProducerWitness S P).quotientWitness = P.toWitness := rfl

end LeanFormal.IUT.XiFPaper.Mzk1A2Node03SourceWitnessConsumerActual
