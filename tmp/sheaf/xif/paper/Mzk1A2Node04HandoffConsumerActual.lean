/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1A2Node03Node04HandoffActual
import Mathlib.Tactic

/-! # A2 node04: handoff consumer -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1A2Node04HandoffConsumerActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.Mzk1A2Node03Node04HandoffActual
open LeanFormal.IUT.XiFPaper.Mzk1A2Node03IntegrationActual

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}

noncomputable def A2Node04HandoffData.toSourceSignQuotientData
    (D : A2Node04HandoffData A) : SourceSignQuotientData A :=
  D.completion.toSourceSignQuotientData

noncomputable def A2Node04HandoffData.toCompletionSignQuotient
    (D : A2Node04HandoffData A) : SourceCompletionSignQuotient A :=
  D.completion

def A2Node04HandoffData.toNode03
    (D : A2Node04HandoffData A) : A2Node03Interface A :=
  D.node03

@[simp] theorem A2Node04HandoffData.toSourceSignQuotientData_xF
    (D : A2Node04HandoffData A) :
    (A2Node04HandoffData.toSourceSignQuotientData D).xF = D.completion.xF := rfl

end LeanFormal.IUT.XiFPaper.Mzk1A2Node04HandoffConsumerActual
