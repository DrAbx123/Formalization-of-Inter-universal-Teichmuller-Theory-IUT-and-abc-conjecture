import tmp.sheaf.xif.paper.Mzk1BetaAvoidingFoldActual
import tmp.sheaf.xif.paper.RestatedLemma24InterfaceActual
import tmp.sheaf.xif.paper.Mzk1Thm25P1CompositeConsumerDesignActual
import tmp.sheaf.xif.paper.Mzk1Thm25P1CompositeConsumerActual
import tmp.sheaf.xif.paper.Mzk1Consumer24AdapterActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

/-!
# Mzk1Consumer24AdapterUnconditionalActual — Problem A fold base wired UNCONDITIONALLY (finite beta)

STEP 0 prior-art (reuse, no re-proof):
* Mzk1BetaAvoidingFoldActual (GREEN): betaAvoiding_all (S : Finset ℚ) (beta : ℚ)
  (hbeta : beta notin S) : BetaAvoidingAt S beta, where BetaAvoidingAt gives q with
  0 < natDegree, q(S) subset {0,1}, q(beta) != 0, q(beta) != 1, CV01 q (all C-point
  critical values in {0,1});
* RestatedLemma24InterfaceActual: Mzk1Lemma24Target / specialSet / polyEvalP1 /
  criticalValuesOverC / CVCompositionLawStatement;
* stepxi Mzk1Thm25P1CompositeConsumerDesignActual: P1CompositeConsumerInputs /
  P1CompositeConsumerStatement / P1CompositeRealConsumerTarget;
* stepxi Mzk1Thm25P1CompositeConsumerActual (CITABLE 12): p1CompositeRealConsumerTarget_rational;
* abc Mzk1Consumer24AdapterActual: p1CompositeRealConsumerTarget_of_statement.

DELIVERED HERE (new file; no green file modified):
(1) FiniteBetaCorrectedBase: for EVERY finite S : Finset (P1Point Q) and EVERY rational
    b with ofFinite b notin S, the restated 2.4 target Mzk1Lemma24Target S (ofFinite b)
    holds — proved DIRECTLY from the fold (betaAvoiding_all).  The infinity point in S
    is harmless: polyEvalP1 q infty = infty in specialSet.
(2) Unconditional h24BaseConcrete for FINITE beta (the named BetaAvoidingBelyiBaseInput
    premise is REMOVED).  SPEC REPAIR: the original BetaAvoidingBelyiBaseInput is FALSE
    for beta = infty (infinity-beta counterexample), so it must not be used; this file
    restricts the base to finite beta only.
(3) A P1CompositeConsumerInputs bundle with the h24Base slot filled by the unconditional
    finite-beta base; h22 / AlgebraicNestedInductionInput / MoebiusData /
    CPointCriticalValueLift remain explicit parameters (nothing asserted true).
SCOPE: finite beta / F=Q component only; the beta = infty case and the full P1(Qbar)
reduction remain NAMED; NO closure claim; gate NOT PASSED; h22 binding HOLD.
Registry frozen 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Consumer24AdapterUnconditionalActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1Thm25P1CompositeConsumerDesignActual
open LeanFormal.IUT.XiFPaper.Mzk1Thm25P1CompositeConsumerActual

/-- The corrected 2.4 base: FINITE beta only (ofFinite b, b : Q). -/
def FiniteBetaCorrectedBase : Prop :=
  forall (S : Finset (P1Point ℚ)) (b : ℚ), P1Point.ofFinite b ∉ S →
    RestatedLemma24InterfaceActual.Mzk1Lemma24Target S (P1Point.ofFinite b)

/-- The finite-beta corrected 2.4 base is PROVED unconditionally from the Problem A fold. -/
theorem finiteBetaCorrectedBase_proved : FiniteBetaCorrectedBase := by
  intro S b hb
  -- use the rational points of S (send the infinity point to b+1, so b is not in S')
  let g : P1Point ℚ → ℚ := fun p =>
    match p with
    | none => b + 1
    | some x => x
  let S' : Finset ℚ := S.image g
  have hb' : b ∉ S' := by
    intro hmem
    obtain ⟨p, hp, hg⟩ := Finset.mem_image.mp hmem
    cases p with
    | none =>
        have h : b + 1 = b := hg
        linarith
    | some x =>
        have hx : x = b := hg
        subst hx
        exact hb (by simpa [P1Point.ofFinite] using hp)
  obtain ⟨q, hdeg, hpresq, hq0, hq1, hCV⟩ :=
    LeanFormal.IUT.XiFPaper.Mzk1BetaAvoidingFoldActual.betaAvoiding_all S' b hb'
  refine ⟨q, hdeg, ?_, ?_, ?_, ?_⟩
  · -- q maps S into the special set {0,1,infinity}
    intro p hp
    cases p with
    | none =>
        simp [RestatedLemma24InterfaceActual.polyEvalP1,
          RestatedLemma24InterfaceActual.specialSet, P1Point.infty]
    | some x =>
        have hx : x ∈ S' := Finset.mem_image.mpr ⟨P1Point.ofFinite x, hp, rfl⟩
        have hval := hpresq x hx
        rcases hval with h0 | h1
        · simp [RestatedLemma24InterfaceActual.polyEvalP1,
            RestatedLemma24InterfaceActual.specialSet, P1Point.ofFinite, h0]
        · simp [RestatedLemma24InterfaceActual.polyEvalP1,
            RestatedLemma24InterfaceActual.specialSet, P1Point.ofFinite, h1]
  · -- q(beta) is outside the special set
    simp [RestatedLemma24InterfaceActual.polyEvalP1,
      RestatedLemma24InterfaceActual.specialSet, P1Point.ofFinite, P1Point.infty, hq0, hq1]
  · -- critical values over C are contained in {0,1}
    intro c hc
    obtain ⟨z, hne, hzder, hzval⟩ := hc
    have hcv := hCV z hzder
    rcases hcv with h0 | h1
    · left
      rw [← hzval]
      exact h0
    · right
      rw [← hzval]
      exact h1
  · -- the C-point implication form
    intro z hval hder
    apply hval
    have hcv := hCV z hder
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hcv

/-- Unconditional finite-beta h24BaseConcrete (replaces the named
BetaAvoidingBelyiBaseInput premise on finite beta). -/
def H24BaseConcreteFinite : Prop := FiniteBetaCorrectedBase

theorem h24BaseConcrete_finite_proved : H24BaseConcreteFinite :=
  finiteBetaCorrectedBase_proved

/-- Pointwise form: every finite beta outside S has the restated 2.4 target. -/
theorem h24BaseConcrete_finite (S : Finset (P1Point ℚ)) (b : ℚ)
    (hb : P1Point.ofFinite b ∉ S) :
    RestatedLemma24InterfaceActual.Mzk1Lemma24Target S (P1Point.ofFinite b) :=
  finiteBetaCorrectedBase_proved S b hb

/-- Construct the consumer input bundle with the h24Base slot filled by the UNCONDITIONAL
finite-beta base; the other slots remain explicit parameters. -/
def p1CompositeConsumerInputs_unconditional24
    (h22 : LeanFormal.IUT.XiFPaper.Mzk1Thm25WiringActual.Lemma22FullStatementShape)
    (hain : LeanFormal.IUT.XiFPaper.RestatedLemma22InterfaceActual.AlgebraicNestedInductionInput)
    (mob : MoebiusData) (hlift : Prop) :
    P1CompositeConsumerInputs :=
  { h22 := h22
    h24Base := H24BaseConcreteFinite
    algebraicNestedInduction := hain
    mobius := mob
    cvCompositionLaw := RestatedLemma24InterfaceActual.CVCompositionLawStatement
    cPointCriticalValueLift := hlift }

/-- The h24Base slot of the bundle is the unconditional finite-beta base. -/
theorem p1CompositeConsumerInputs_unconditional24_h24Base
    (h22 : LeanFormal.IUT.XiFPaper.Mzk1Thm25WiringActual.Lemma22FullStatementShape)
    (hain : LeanFormal.IUT.XiFPaper.RestatedLemma22InterfaceActual.AlgebraicNestedInductionInput)
    (mob : MoebiusData) (hlift : Prop) :
    (p1CompositeConsumerInputs_unconditional24 h22 hain mob hlift).h24Base =
      H24BaseConcreteFinite := rfl

/-- The bundle's h24Base slot is PROVED (unconditional, finite beta). -/
theorem p1CompositeConsumerInputs_unconditional24_h24Base_proved
    (h22 : LeanFormal.IUT.XiFPaper.Mzk1Thm25WiringActual.Lemma22FullStatementShape)
    (hain : LeanFormal.IUT.XiFPaper.RestatedLemma22InterfaceActual.AlgebraicNestedInductionInput)
    (mob : MoebiusData) (hlift : Prop) :
    (p1CompositeConsumerInputs_unconditional24 h22 hain mob hlift).h24Base :=
  h24BaseConcrete_finite_proved

/-- The real consumer statement holds for the unconditional finite-beta bundle (via the
PROVED F=Q consumer target). -/
theorem p1CompositeConsumerStatement_unconditional24
    (h22 : LeanFormal.IUT.XiFPaper.Mzk1Thm25WiringActual.Lemma22FullStatementShape)
    (hain : LeanFormal.IUT.XiFPaper.RestatedLemma22InterfaceActual.AlgebraicNestedInductionInput)
    (mob : MoebiusData) (hlift : Prop) :
    P1CompositeConsumerStatement
      (p1CompositeConsumerInputs_unconditional24 h22 hain mob hlift) :=
  p1CompositeRealConsumerTarget_rational

/-- The real P1 composite consumer target for the unconditional finite-beta bundle (via
abc's statement transport). -/
theorem p1CompositeRealConsumerTarget_unconditional24
    (h22 : LeanFormal.IUT.XiFPaper.Mzk1Thm25WiringActual.Lemma22FullStatementShape)
    (hain : LeanFormal.IUT.XiFPaper.RestatedLemma22InterfaceActual.AlgebraicNestedInductionInput)
    (mob : MoebiusData) (hlift : Prop) :
    P1CompositeRealConsumerTarget :=
  LeanFormal.IUT.XiFPaper.Mzk1Consumer24AdapterActual.p1CompositeRealConsumerTarget_of_statement
    (p1CompositeConsumerInputs_unconditional24 h22 hain mob hlift)
    (p1CompositeConsumerStatement_unconditional24 h22 hain mob hlift)

/-- Adapter rows: (component, evidence, status/scope). -/
def unconditional24AdapterRows : List (String × String × String) :=
  [ ("Problem A fold base (finite beta)", "Mzk1BetaAvoidingFoldActual.betaAvoiding_all", "GREen/PROVED"),
    ("finite-beta corrected 2.4 base", "FiniteBetaCorrectedBase (forall finite S, b, ofFinite b notin S -> Mzk1Lemma24Target S (ofFinite b))", "PROVED (finiteBetaCorrectedBase_proved)"),
    ("unconditional h24BaseConcrete (finite beta)", "H24BaseConcreteFinite / h24BaseConcrete_finite_proved", "PROVED UNCONDITIONALLY"),
    ("infinity-beta spec repair", "original BetaAvoidingBelyiBaseInput FALSE for beta = infinity; NOT used", "SPEC REPAIR (recorded)"),
    ("h24Base consumer slot", "p1CompositeConsumerInputs_unconditional24_h24Base(_proved)", "FILLED UNCONDITIONALLY"),
    ("remaining explicit parameters", "h22 (Lemma22FullStatementShape) / AlgebraicNestedInductionInput / MoebiusData / CPointCriticalValueLift", "EXPLICIT PARAMETERS (not asserted)"),
    ("consumer statement / target", "p1CompositeConsumerStatement_unconditional24 + p1CompositeRealConsumerTarget_unconditional24 (via abc adapter transport + PROVED F=Q target)", "PROVED (finite beta / F=Q scope)"),
    ("scope", "finite beta only; beta = infinity excluded; full P1(Qbar) reduction NAMED; no closure claim", "SCOPE"),
    ("status", "gate NOT PASSED; h22 binding HOLD; pins 14041", "INTEGRITY") ]

theorem unconditional24AdapterRows_length : unconditional24AdapterRows.length = 9 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Consumer24AdapterUnconditionalActual

end
