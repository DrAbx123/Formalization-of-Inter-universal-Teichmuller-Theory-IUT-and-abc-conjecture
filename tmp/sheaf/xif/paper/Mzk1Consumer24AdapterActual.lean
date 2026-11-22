import Mathlib
import tmp.sheaf.xif.paper.Mzk1Thm25P1CompositeConsumerDesignActual
import tmp.sheaf.xif.paper.Mzk1Lemma24BaseProviderRestatedActual
import tmp.sheaf.xif.paper.RestatedLemma24CVLawActual
import tmp.sheaf.xif.paper.RestatedLemma22InterfaceActual
import LeanFormal.IUT.Audit.Status

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Consumer24AdapterActual

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1Thm25P1CompositeConsumerDesignActual
open LeanFormal.IUT.XiFPaper.Mzk1Thm25WiringActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24InductionActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24CVLawActual
open LeanFormal.IUT.XiFPaper.RestatedLemma22InterfaceActual

/-- Concrete instantiation of the consumer's 2.4 base slot (F = Q scope): the named
beta-avoiding Belyi base input yields the restated 2.4 target for every rational state. -/
def h24BaseConcrete : Prop :=
  ∀ (S : Finset (P1Point ℚ)) (β : P1Point ℚ), β ∉ S → Mzk1Lemma24Target S β

/-- The concrete 2.4 base slot is filled CONDITIONALLY by the named class-B input. -/
theorem h24BaseConcrete_of_BetaAvoidingBelyiBase (h : BetaAvoidingBelyiBaseInput) :
    h24BaseConcrete :=
  h

/-- Construct the real consumer's input bundle with the 2.4 base slot filled by the
concrete conditional target and the CV composition law slot filled by the PROVED law.
The remaining slots are explicit parameters (h22 gate, paper-scope named input, Moebius
data, C-point lift slot); no slot is asserted true by this construction. -/
def p1CompositeConsumerInputs_of_conditional24
    (h22 : Lemma22FullStatementShape)
    (hbase : BetaAvoidingBelyiBaseInput)
    (hain : AlgebraicNestedInductionInput)
    (mob : MoebiusData) (hlift : Prop) :
    P1CompositeConsumerInputs :=
  { h22 := h22
    h24Base := h24BaseConcrete
    algebraicNestedInduction := hain
    mobius := mob
    cvCompositionLaw := CVCompositionLawStatement
    cPointCriticalValueLift := hlift }

/-- The conditional consumer statement transports to the real consumer target once the
named consumer statement hypothesis is supplied (statement layer only). -/
theorem p1CompositeRealConsumerTarget_of_statement
    (I : P1CompositeConsumerInputs) (h : P1CompositeConsumerStatement I) :
    P1CompositeRealConsumerTarget :=
  h

/-- Adapter rows: how the 2.4 conditional base feeds the real P1 composite consumer. -/
def consumer24AdapterRows : List (String × String × String) :=
  [ ("2.4 base slot", "h24BaseConcrete = conditional rational 2.4 target (hbase named class-B)", "FILLED CONDITIONALLY (BetaAvoidingBelyiBaseInput; no closure)"),
    ("CV composition law slot", "CVCompositionLawStatement", "FILLED WITH PROVED LAW (RestatedLemma24CVLawActual)"),
    ("2.2 gate slot", "Lemma22FullStatementShape", "PARAMETER (upstream gate; binding HOLD)"),
    ("paper-scope slot", "AlgebraicNestedInductionInput", "PARAMETER (named class-B paper 179-206)"),
    ("Moebius slot", "MoebiusData", "PARAMETER (qpilot rational Moebius layer)"),
    ("C-point lift slot", "Prop parameter hlift", "PARAMETER (upstream obligation)"),
    ("consumer statement", "P1CompositeConsumerStatement I => P1CompositeRealConsumerTarget", "PROVED (statement transport)"),
    ("scope", "F=Q component only; full P1(Qbar) reduction NAMED", "SCOPE / NO CLOSURE"),
    ("status", "binding HOLD; gate NOT PASSED; pins 14041", "INTEGRITY") ]

theorem consumer24AdapterRows_length : consumer24AdapterRows.length = 9 := rfl

/-- Status: 2.4 conditional base wired into the real P1 composite consumer inputs (F=Q
scope); CV law slot filled with a PROVED law; all other slots explicit parameters; no
closure claim. -/
def Consumer24AdapterStatus : Audit.Obligation :=
  { id := "MZK1.thm25.consumer24-adapter"
    source := "Mzk1Thm25P1CompositeConsumerDesignActual (stepxi); Lead A313/A318; paper Lemma 2.4 F=Q component"
    status := Audit.VerificationStatus.interface
    note := "ADAPTER (conditional): h24BaseConcrete = conditional rational 2.4 target supplied by BetaAvoidingBelyiBaseInput (named class-B); consumer input bundle constructor p1CompositeConsumerInputs_of_conditional24 fills h24Base with that concrete Prop and cvCompositionLaw with the PROVED CVCompositionLawStatement, leaving h22/algebraicNestedInduction/mobius/cPointCriticalValueLift as explicit parameters (not asserted true); p1CompositeRealConsumerTarget_of_statement transports the named consumer statement. Scope F=Q component only; full P1(Qbar) reduction NAMED; no closure; binding HOLD; gate NOT PASSED; registry frozen 14041."
    dependsOn := [ "MZK1.lemma24.base-provider-restated", "MZK1.thm25.p1-composite-consumer" ]
    sorryItems :=
      [ "BetaAvoidingBelyiBaseInput (named class-B)",
        "Lemma22FullStatementShape (upstream gate, binding HOLD)",
        "CPointCriticalValueLift (upstream obligation)" ] }

#check p1CompositeConsumerInputs_of_conditional24
#check p1CompositeRealConsumerTarget_of_statement
end LeanFormal.IUT.XiFPaper.Mzk1Consumer24AdapterActual
end