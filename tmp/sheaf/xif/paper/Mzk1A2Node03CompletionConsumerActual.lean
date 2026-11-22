/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1A2Node03IntegrationConsumerActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceCompletion
import Mathlib.Tactic

/-! # A2 node03 -> SourceCompletionSignQuotient consumer -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1A2Node03CompletionConsumerActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.Mzk1A2Node03IntegrationActual
open LeanFormal.IUT.XiFPaper.Mzk1A2Node03IntegrationConsumerActual

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}

noncomputable def A2Node03Interface.toSourceCompletionSignQuotient
    (D : A2Node03Interface A) :
    SourceCompletionSignQuotient A :=
  SourceCompletionSignQuotient.ofSourceSignQuotientData D.toSourceSignQuotientData

@[simp] theorem A2Node03Interface.toSourceCompletionSignQuotient_quotientWitness
    (D : A2Node03Interface A) :
    (A2Node03Interface.toSourceCompletionSignQuotient D).quotientWitness = D.toWitness := rfl

end LeanFormal.IUT.XiFPaper.Mzk1A2Node03CompletionConsumerActual
