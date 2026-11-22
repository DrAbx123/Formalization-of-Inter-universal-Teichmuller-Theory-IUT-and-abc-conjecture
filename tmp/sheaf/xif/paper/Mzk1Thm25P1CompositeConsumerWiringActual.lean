import tmp.sheaf.xif.paper.Mzk1Thm25P1CompositeConsumerActual
import tmp.sheaf.xif.paper.Mzk1Consumer24AdapterActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# Mzk1Thm25P1CompositeConsumerWiringActual — 2.4 base adapter WIRED into the real consumer

STEP 0 prior-art (reuse, no re-proof):
* stepxi Mzk1Thm25P1CompositeConsumerActual (CITABLE 12): p1CompositeRealConsumerTarget_rational
  (P1CompositeRealConsumerTarget PROVED at F=Q scope) and
  p1Composite_mapPoints_consumer_rational (2.2 o 2.3 inversion composition);
* abc Mzk1Consumer24AdapterActual (CITABLE): h24BaseConcrete (conditional rational 2.4
  target), h24BaseConcrete_of_BetaAvoidingBelyiBase, p1CompositeConsumerInputs_of_conditional24
  (builds stepxi's input bundle with h24Base filled from the named class-B input and
  cvCompositionLaw filled with the PROVED CVCompositionLawStatement),
  p1CompositeRealConsumerTarget_of_statement (statement transport).

DELIVERED HERE:
* the input bundle built by the adapter has its h24Base slot equal to the concrete
  conditional 2.4 target and its cvCompositionLaw slot equal to the PROVED CV law;
* the real consumer statement holds for that bundle (via stepxi's PROVED
  p1CompositeRealConsumerTarget_rational), and the adapter's statement transport yields
  the real consumer target.
SCOPE: F=Q component only; full P1(Qbar) reduction NAMED; NO closure claim; gate NOT
PASSED; h22 binding HOLD.  Registry frozen 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Thm25P1CompositeConsumerWiringActual

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1Thm25P1CompositeConsumerDesignActual
open LeanFormal.IUT.XiFPaper.Mzk1Thm25P1CompositeConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1Consumer24AdapterActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24CVLawActual
open LeanFormal.IUT.XiFPaper.Mzk1Thm25WiringActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24InductionActual

/-- The adapter's input bundle fills the 2.4 base slot with the concrete conditional
rational 2.4 target. -/
theorem wiredInputs_h24Base_eq
    (h22 : Lemma22FullStatementShape) (hbase : BetaAvoidingBelyiBaseInput)
    (hain : LeanFormal.IUT.XiFPaper.RestatedLemma22InterfaceActual.AlgebraicNestedInductionInput) (mob : MoebiusData) (hlift : Prop) :
    (p1CompositeConsumerInputs_of_conditional24 h22 hbase hain mob hlift).h24Base =
      h24BaseConcrete := rfl

/-- The adapter's input bundle fills the CV composition law slot with the PROVED
CVCompositionLawStatement. -/
theorem wiredInputs_cvLaw_eq
    (h22 : Lemma22FullStatementShape) (hbase : BetaAvoidingBelyiBaseInput)
    (hain : LeanFormal.IUT.XiFPaper.RestatedLemma22InterfaceActual.AlgebraicNestedInductionInput) (mob : MoebiusData) (hlift : Prop) :
    (p1CompositeConsumerInputs_of_conditional24 h22 hbase hain mob hlift).cvCompositionLaw =
      LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual.CVCompositionLawStatement := rfl

/-- The 2.4 base slot is filled CONDITIONALLY by the named beta-avoiding Belyi base input. -/
theorem wiredInputs_h24Base_supplied
    (hbase : BetaAvoidingBelyiBaseInput) :
    h24BaseConcrete :=
  h24BaseConcrete_of_BetaAvoidingBelyiBase hbase

/-- The real consumer statement holds for the adapter-built input bundle (F=Q scope),
using stepxi's PROVED p1CompositeRealConsumerTarget_rational. -/
theorem wiredStatement_holds
    (h22 : Lemma22FullStatementShape) (hbase : BetaAvoidingBelyiBaseInput)
    (hain : LeanFormal.IUT.XiFPaper.RestatedLemma22InterfaceActual.AlgebraicNestedInductionInput) (mob : MoebiusData) (hlift : Prop) :
    P1CompositeConsumerStatement
      (p1CompositeConsumerInputs_of_conditional24 h22 hbase hain mob hlift) :=
  p1CompositeRealConsumerTarget_rational

/-- The adapter's statement transport yields the real P1 composite consumer target for
the wired input bundle (F=Q scope). -/
theorem p1CompositeRealConsumerTarget_wired
    (h22 : Lemma22FullStatementShape) (hbase : BetaAvoidingBelyiBaseInput)
    (hain : LeanFormal.IUT.XiFPaper.RestatedLemma22InterfaceActual.AlgebraicNestedInductionInput) (mob : MoebiusData) (hlift : Prop) :
    P1CompositeRealConsumerTarget :=
  p1CompositeRealConsumerTarget_of_statement
    (p1CompositeConsumerInputs_of_conditional24 h22 hbase hain mob hlift)
    (wiredStatement_holds h22 hbase hain mob hlift)

/-- Wiring rows: (component, evidence, status/scope). -/
def consumerWiringRows : List (String × String × String) :=
  [ ("2.2 o 2.3 real consumer (F=Q)", "Mzk1Thm25P1CompositeConsumerActual.p1CompositeRealConsumerTarget_rational", "USED (CITABLE 12)"),
    ("2.4 base adapter", "Mzk1Consumer24AdapterActual.p1CompositeConsumerInputs_of_conditional24 (h24Base := h24BaseConcrete; cvCompositionLaw := CVCompositionLawStatement)", "USED (abc, CITABLE)"),
    ("h24Base slot value", "wiredInputs_h24Base_eq (rfl) + wiredInputs_h24Base_supplied (named class-B input)", "FILLED CONDITIONALLY"),
    ("CV law slot value", "wiredInputs_cvLaw_eq (PROVED law)", "FILLED WITH PROVED LAW"),
    ("consumer statement for wired bundle", "wiredStatement_holds", "PROVED (F=Q scope)"),
    ("statement transport", "p1CompositeRealConsumerTarget_of_statement -> p1CompositeRealConsumerTarget_wired", "PROVED"),
    ("scope", "F=Q component only; full P1(Qbar) reduction NAMED; explicit parameter slots: h22 gate, AlgebraicNestedInductionInput, MoebiusData, CPointCriticalValueLift", "SCOPE / NO CLOSURE"),
    ("status", "binding HOLD; gate NOT PASSED; pins 14041", "INTEGRITY") ]

theorem consumerWiringRows_length : consumerWiringRows.length = 8 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Thm25P1CompositeConsumerWiringActual

end
