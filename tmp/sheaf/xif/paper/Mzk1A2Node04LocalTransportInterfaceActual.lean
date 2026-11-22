/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1A2Node04HandoffConsumerActual
import tmp.sheaf.xif.paper.Mzk1A2Node03Node04HandoffActual
import tmp.sheaf.xif.paper.Mzk1TaskECompletionFieldEquivActual
import tmp.sheaf.xif.paper.Mzk1TaskEIntegersRingEquivActual
import tmp.sheaf.xif.paper.Mzk1TaskEUnitsTorsionActual
import Mathlib.Tactic

/-! # A2 node04 local transport / unit quotient handoff interface -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1A2Node04LocalTransportInterfaceActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.Mzk1A2Node04HandoffConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1A2Node03Node04HandoffActual
open LeanFormal.IUT.XiFPaper.Mzk1TaskECompletionFieldEquivActual
open LeanFormal.IUT.XiFPaper.Mzk1TaskEIntegersRingEquivActual
open LeanFormal.IUT.XiFPaper.Mzk1TaskEUnitsTorsionActual

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}

/-- Exact node04 handoff data to the local field/integer/unit-quotient
consumers; no inhabitant is supplied. -/
structure A2Node04LocalTransportInterface (A : InitialThetaArithmeticData l) where
  handoff : A2Node04HandoffData A
  completionFieldEquiv : CompletionFieldQFiveEquiv
  integersEquiv : IntegersCompletionFieldZFiveEquiv
  unitsTorsionEquiv : UnitsTorsionQuotientEquiv

def A2Node04LocalTransportInterface.toHandoff
    (D : A2Node04LocalTransportInterface A) : A2Node04HandoffData A :=
  D.handoff

def A2Node04LocalTransportInterfaceRequired : Prop :=
  Nonempty (A2Node04LocalTransportInterface A)

end LeanFormal.IUT.XiFPaper.Mzk1A2Node04LocalTransportInterfaceActual
