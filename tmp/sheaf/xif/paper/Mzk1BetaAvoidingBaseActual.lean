import Mathlib
import tmp.sheaf.xif.paper.Mzk1BetaAvoidingFoldActual
import tmp.sheaf.xif.paper.RestatedLemma24InductionActual
import tmp.sheaf.xif.paper.Mzk1Lemma24BaseProviderRestatedActual

/-!
# Mzk1BetaAvoidingBaseActual — the PROVED fold theorem wired into the restated Lemma 2.4 base

Base input of the restated Lemma 2.4 induction (F = Q component), plus the refutation of
the named input as previously stated.

## Spec bug found in the named base input

RestatedLemma24InductionActual.BetaAvoidingBelyiBaseInput (and the identically stated
Mzk1Lemma24CorrectedStatement, and RestatedInductionConclusion) quantify beta over ALL of
P1Point Q = Option Q, i.e. including beta = P1Point.infty.  But polyEvalP1 q p =
p.map (fun x => eval x q), so for p = infty = none we have polyEvalP1 q infty = infty for
EVERY q, and infty is one of the three points of specialSet Q.  Hence the avoidance
condition polyEvalP1 q beta notin specialSet Q is UNSATISFIABLE at beta = infty, and every
statement of the form "for all S, beta (outside S), there is q ..." with beta ranging over
P1Point Q is FALSE — independently of the nonconstancy, of the map on S, and of the
critical values.  This file proves that refutation (not_betaAvoidingBelyiBaseInput) and
the sharper pointwise form (not_mzk1Lemma24Target_infty).

This is a statement-layer defect only: the finite-beta content is exactly what the fold
induction of Mzk1BetaAvoidingFoldActual (Problem A, PROVED) supplies.

## Corrected input, now PROVED

BetaAvoidingBelyiBaseInputCorrected restricts beta to finite points P1Point.ofFinite b
(b : Q).  It is PROVED here (betaAvoidingBelyiBaseInputCorrected_proved) by

1. extracting from S : Finset (P1Point Q) the finset Sf : Finset Q of the finite points
   of S (Finset.filterMap (fun p : Option Q => p) S — the hint's filterMap, with the
   injectivity obligation that this Mathlib's Finset.filterMap requires);
2. b notin Sf because a preimage would be P1Point.ofFinite b in S, contradicting the
   hypothesis;
3. applying Mzk1BetaAvoidingFoldActual.betaAvoiding_all Sf b to get a nonconstant
   q : Q[X] with q(Sf) subset {0,1}, q(b) notin {0,1} and CV01 q;
4. re-reading this for Mzk1Lemma24Target S (P1Point.ofFinite b):
   * each finite point of S lands in {0,1} subset specialSet;
   * the point infty of S maps to infty in specialSet (so the quantification over
     infty inside S is harmless — this is precisely the asymmetry the bug turned on);
   * polyEvalP1 q (ofFinite b) = ofFinite (q.eval b) notin specialSet from the two
     inequalities;
   * criticalValuesOverC q subset {0,1} and the unramified-off-{0,1} condition are the
     contrapositive of CV01 q.

No sorry, no new axioms, no PUnit/True placeholders.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1BetaAvoidingBaseActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24InductionActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma24BaseProviderRestatedActual
open LeanFormal.IUT.XiFPaper.Mzk1BetaAvoidingFoldActual

/-! ## 1. The obstruction at beta = infinity -/

/-- On P1Point, evaluation of a polynomial sends the point at infinity to itself
(none.map f = none). -/
theorem polyEvalP1_infty (q : Polynomial ℚ) :
    polyEvalP1 q (P1Point.infty : P1Point ℚ) = P1Point.infty := rfl

/-- The point at infinity is one of the Belyi special points
specialSet Q = {infty, 0, 1}. -/
theorem infty_mem_specialSet : (P1Point.infty : P1Point ℚ) ∈ specialSet ℚ := by
  simp [specialSet]

/-- **Pointwise refutation**: for every finite point set S, the restated Lemma 2.4
target is FALSE at beta = infty: whatever q is, polyEvalP1 q infty = infty lies in
specialSet Q, so the avoidance clause can never hold. -/
theorem not_mzk1Lemma24Target_infty (S : Finset (P1Point ℚ)) :
    ¬ Mzk1Lemma24Target S (P1Point.infty : P1Point ℚ) := by
  rintro ⟨q, -, -, havoid, -, -⟩
  apply havoid
  rw [polyEvalP1_infty]
  exact infty_mem_specialSet

/-- **The named base input is FALSE** (not merely unproved): take S = emptyset and
beta = infty.  This is the spec bug found in BetaAvoidingBelyiBaseInput. -/
theorem not_betaAvoidingBelyiBaseInput : ¬ BetaAvoidingBelyiBaseInput := by
  intro h
  exact not_mzk1Lemma24Target_infty ∅ (h ∅ (P1Point.infty : P1Point ℚ) (by simp))

/-- The interface's Mzk1Lemma24CorrectedStatement has the same statement as the named
base input, hence it is FALSE for the same reason. -/
theorem not_mzk1Lemma24CorrectedStatement : ¬ Mzk1Lemma24CorrectedStatement :=
  not_betaAvoidingBelyiBaseInput

/-- The restated induction conclusion RestatedInductionConclusion (which quantifies beta
over all of P1Point Q) is FALSE for the same reason: the state (emptyset, infty)
satisfies the hypothesis beta notin S. -/
theorem not_restatedInductionConclusion : ¬ RestatedInductionConclusion := by
  intro h
  exact not_mzk1Lemma24Target_infty ∅ (h (∅, (P1Point.infty : P1Point ℚ)) (by simp))

/-- The induction's base statement RestatedBaseStatement is also FALSE as stated, for
every measure that vanishes at the state (emptyset, infty): that state has measure
(0, 0) but no target.  (The finite-beta restriction in RestatedBaseStatementFinite is
therefore necessary.) -/
theorem not_restatedBaseStatement (μ : RestatedState → Nat × Nat)
    (hμ : μ (∅, (P1Point.infty : P1Point ℚ)) = (0, 0)) : ¬ RestatedBaseStatement μ := by
  intro h
  exact not_mzk1Lemma24Target_infty ∅ (h (∅, (P1Point.infty : P1Point ℚ)) hμ (by simp))

/-! ## 2. Corrected finite-beta base input -/

/-- **Corrected base input**: the beta-avoiding rational Belyi base with the point beta
restricted to finite points of P^1(Q) (P1Point.ofFinite b).  This is the form in
which the statement is actually true. -/
def BetaAvoidingBelyiBaseInputCorrected : Prop :=
  ∀ (S : Finset (P1Point ℚ)) (b : ℚ),
    P1Point.ofFinite b ∉ S → Mzk1Lemma24Target S (P1Point.ofFinite b)

/-- **The corrected base input is PROVED** from the fold theorem
Mzk1BetaAvoidingFoldActual.betaAvoiding_all (Problem A). -/
theorem betaAvoidingBelyiBaseInputCorrected_proved : BetaAvoidingBelyiBaseInputCorrected := by
  intro S b hb
  classical
  -- The finset of finite points of S, via the hint's filterMap.
  have hf_inj : ∀ a a' : Option ℚ, ∀ x : ℚ, x ∈ (fun p : Option ℚ => p) a →
      x ∈ (fun p : Option ℚ => p) a' → a = a' := by
    intro a a' x ha ha'
    have ha1 : a = some x := ha
    have ha2 : a' = some x := ha'
    rw [ha1, ha2]
  -- b is not among the finite points of S.
  have hbSf : b ∉ Finset.filterMap (fun p : Option ℚ => p) S hf_inj := by
    rw [Finset.mem_filterMap]
    rintro ⟨p, hpS, hfp⟩
    have hp : p = P1Point.ofFinite b := hfp
    exact hb (hp ▸ hpS)
  -- Problem A (fold induction) for the finite set of finite points.
  obtain ⟨q, hqdeg, hqS, hqb0, hqb1, hqcv⟩ :=
    betaAvoiding_all (Finset.filterMap (fun p : Option ℚ => p) S hf_inj) b hbSf
  refine ⟨q, hqdeg, ?_, ?_, ?_, ?_⟩
  · -- q maps S into specialSet Q = {infty, 0, 1}.
    intro p hp
    cases p with
    | none =>
      exact infty_mem_specialSet
    | some x =>
      have hxSf : x ∈ Finset.filterMap (fun p : Option ℚ => p) S hf_inj := by
        rw [Finset.mem_filterMap]
        exact ⟨some x, hp, rfl⟩
      rcases hqS x hxSf with h0 | h1
      · simp [polyEvalP1, specialSet, P1Point.ofFinite, h0]
      · simp [polyEvalP1, specialSet, P1Point.ofFinite, h1]
  · -- q (ofFinite b) avoids specialSet.
    intro hmem
    have hval : polyEvalP1 q (P1Point.ofFinite b) = P1Point.ofFinite (q.eval b) := rfl
    rw [hval] at hmem
    have hcases : q.eval b = 0 ∨ q.eval b = 1 := by
      simpa [specialSet, P1Point.ofFinite, P1Point.infty] using hmem
    rcases hcases with h | h
    · exact hqb0 h
    · exact hqb1 h
  · -- Critical values over C lie in {0,1}.
    rintro c ⟨z, -, hderz, hcz⟩
    rw [← hcz]
    simpa using hqcv z hderz
  · -- Unramified away from {0,1}: contrapositive of CV01 q.
    intro z hz hderz
    exact hz (by simpa using hqcv z hderz)

/-- Item of the requested interface: the restated target for every finite beta. -/
theorem Mzk1Lemma24Target_finite_beta (S : Finset (P1Point ℚ)) (b : ℚ)
    (hb : P1Point.ofFinite b ∉ S) : Mzk1Lemma24Target S (P1Point.ofFinite b) :=
  betaAvoidingBelyiBaseInputCorrected_proved S b hb

/-! ## 3. Consumer specialization -/

/-- The corrected form of the conclusion RestatedInductionConclusion: only finite beta.
(No uniform statement over all of P1Point Q can hold, by
not_restatedInductionConclusion.) -/
def RestatedInductionConclusionFinite : Prop :=
  ∀ (S : Finset (P1Point ℚ)) (b : ℚ),
    P1Point.ofFinite b ∉ S → Mzk1Lemma24Target S (P1Point.ofFinite b)

/-- The corrected conclusion, PROVED (it is the corrected base input). -/
theorem restatedInductionConclusionFinite_proved : RestatedInductionConclusionFinite :=
  betaAvoidingBelyiBaseInputCorrected_proved

/-- Consumer restated: the old conditional consumer
Mzk1Lemma24BaseProviderRestatedActual.s3135_target_of_betaAvoidingBelyiBase takes the
FALSE input.  This is its corrected counterpart, from the PROVED finite-beta input. -/
theorem s3135_target_of_betaAvoidingBelyiBaseCorrected
    (h : BetaAvoidingBelyiBaseInputCorrected) :
    ∀ (S : Finset (P1Point ℚ)) (b : ℚ),
      P1Point.ofFinite b ∉ S → Mzk1Lemma24Target S (P1Point.ofFinite b) :=
  h

/-- The old consumer's hypothesis is empty: the named input yields False. -/
theorem s3135_target_of_betaAvoidingBelyiBase_vacuous
    (h : BetaAvoidingBelyiBaseInput) : False :=
  not_betaAvoidingBelyiBaseInput h

/-- The induction's base statement RestatedBaseStatement restricted to finite beta
(the only satisfiable form), PROVED for every measure mu. -/
def RestatedBaseStatementFinite (μ : RestatedState → Nat × Nat) : Prop :=
  ∀ (st : RestatedState) (b : ℚ), st.2 = P1Point.ofFinite b → μ st = (0, 0) →
    st.2 ∉ st.1 → Mzk1Lemma24Target st.1 st.2

/-- The finite-beta base statement holds for every measure mu. -/
theorem restatedBaseStatementFinite_proved (μ : RestatedState → Nat × Nat) :
    RestatedBaseStatementFinite μ := by
  intro st b hb hμ hmem
  rw [hb] at hmem ⊢
  exact Mzk1Lemma24Target_finite_beta st.1 b hmem

end LeanFormal.IUT.XiFPaper.Mzk1BetaAvoidingBaseActual
end
