/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1A2Node04LocalTransportInterfaceActual
import tmp.sheaf.xif.paper.Mzk1A2Node03Node04HandoffActual
import tmp.sheaf.xif.paper.Mzk1A2Node04HandoffConsumerActual
import tmp.sheaf.xif.paper.Mzk1A2Node03IntegrationActual
import Mathlib.Tactic

/-! # A2 node04 local transport consumer -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1A2Node04LocalTransportConsumerActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.Mzk1A2Node04LocalTransportInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1A2Node03Node04HandoffActual
open LeanFormal.IUT.XiFPaper.Mzk1A2Node04HandoffConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1A2Node03IntegrationActual
open LeanFormal.IUT.XiFPaper.Mzk1TaskECompletionFieldEquivActual
open LeanFormal.IUT.XiFPaper.Mzk1TaskEIntegersRingEquivActual
open LeanFormal.IUT.XiFPaper.Mzk1TaskEUnitsTorsionActual

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}

def A2Node04LocalTransportInterface.completionFieldEquiv'
    (D : A2Node04LocalTransportInterface A) : CompletionFieldQFiveEquiv :=
  D.completionFieldEquiv

def A2Node04LocalTransportInterface.integersEquiv'
    (D : A2Node04LocalTransportInterface A) : IntegersCompletionFieldZFiveEquiv :=
  D.integersEquiv

def A2Node04LocalTransportInterface.unitsTorsionEquiv'
    (D : A2Node04LocalTransportInterface A) : UnitsTorsionQuotientEquiv :=
  D.unitsTorsionEquiv

theorem A2Node04LocalTransportInterface.nonempty_handoff
    (D : A2Node04LocalTransportInterface A) :
    Nonempty (A2Node04HandoffData A) :=
  ⟨D.handoff⟩


noncomputable def A2Node04LocalTransportInterface.toSourceCompletionSignQuotient
    (D : A2Node04LocalTransportInterface A) : SourceCompletionSignQuotient A :=
  D.handoff.completion

noncomputable def A2Node04LocalTransportInterface.toSourceSignQuotientData
    (D : A2Node04LocalTransportInterface A) : SourceSignQuotientData A :=
  SourceCompletionSignQuotient.toSourceSignQuotientData D.handoff.completion


@[simp] theorem A2Node04LocalTransportInterface.toSourceCompletionSignQuotient_eq
    (D : A2Node04LocalTransportInterface A) :
    A2Node04LocalTransportInterface.toSourceCompletionSignQuotient D = D.handoff.completion := rfl

@[simp] theorem A2Node04LocalTransportInterface.toSourceSignQuotientData_xF
    (D : A2Node04LocalTransportInterface A) :
    (A2Node04LocalTransportInterface.toSourceSignQuotientData D).xF = D.handoff.completion.xF := rfl


@[simp] theorem A2Node04LocalTransportInterface.toSourceSignQuotientData_V
    (D : A2Node04LocalTransportInterface A) :
    (A2Node04LocalTransportInterface.toSourceSignQuotientData D).V =
      D.handoff.completion.V := rfl


def A2Node04LocalTransportInterface.toNode03
    (D : A2Node04LocalTransportInterface A) : A2Node03Interface A :=
  D.handoff.node03

@[simp] theorem A2Node04LocalTransportInterface.toNode03_eq_handoff_node03
    (D : A2Node04LocalTransportInterface A) :
    A2Node04LocalTransportInterface.toNode03 D = D.handoff.node03 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1A2Node04LocalTransportConsumerActual
