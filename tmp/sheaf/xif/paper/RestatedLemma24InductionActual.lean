import Mathlib
import tmp.sheaf.xif.paper.RestatedLemma24InterfaceActual
import tmp.sheaf.xif.paper.Mzk1Lemma24Proof2Actual
import LeanFormal.IUT.Audit.Status

noncomputable section

namespace LeanFormal.IUT.XiFPaper.RestatedLemma24InductionActual

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma24ProofActual

/-- Evaluation of composite polynomials on P^1(Q): polyEvalP1 (r.comp q) = polyEvalP1 r
after polyEvalP1 q. -/
theorem s3135_polyEvalP1_comp (q r : Polynomial ℚ) (p : P1Point ℚ) :
    polyEvalP1 (r.comp q) p = polyEvalP1 r (polyEvalP1 q p) := by
  cases p with
  | none => rfl
  | some x => simp [polyEvalP1, Polynomial.eval_comp]

/-- **CV invariant is preserved by composition** (the corrected 2.4 induction's CV
accounting): if q has the CVInvariant on S, q maps S into S', r has the CVInvariant on
S', r maps the Belyi special set into itself (through the explicit hypotheses at 0 and 1),
and r's critical values lie in {0,1}, then r.comp q has the CVInvariant on S.  Consumes
the CV composition law and special-set preservation statements agreed with stage4/hull. -/
theorem s3135_CVInvariant_comp (hCV : CVCompositionLawStatement)
    (hSS : SpecialSetPreservationStatement) {q r : Polynomial ℚ}
    {S S' : Finset (P1Point ℚ)}
    (hq : CVInvariant S q) (hr_pos : 0 < r.natDegree)
    (hmaps : ∀ p ∈ S, polyEvalP1 q p ∈ S')
    (hr : ∀ p ∈ S', polyEvalP1 r p ∈ specialSet ℚ)
    (hrcv : criticalValuesOverC r ⊆ ({0, 1} : Set ℂ))
    (hr0 : Polynomial.aeval (0 : ℂ) r ∈ ({0, 1} : Set ℂ))
    (hr1 : Polynomial.aeval (1 : ℂ) r ∈ ({0, 1} : Set ℂ)) :
    CVInvariant S (r.comp q) := by
  obtain ⟨hq_pos, hq_map, hq_cv⟩ := hq
  refine ⟨?_, ?_, ?_⟩
  · rw [Polynomial.natDegree_comp]
    exact Nat.mul_pos hr_pos hq_pos
  · intro p hp
    rw [s3135_polyEvalP1_comp]
    exact hr _ (hmaps p hp)
  · intro c hc
    have hsub := hCV q r hc
    rcases hsub with h | h
    · obtain ⟨d, hd, rfl⟩ := h
      exact hSS r hr0 hr1 d (hq_cv hd)
    · exact hrcv h

/-- State of the corrected nested induction: finite set of rational points plus beta. -/
abbrev RestatedState : Type := Finset (P1Point ℚ) × P1Point ℚ

/-- Corrected induction conclusion: the restated target for every state with beta outside
the current set. -/
def RestatedInductionConclusion : Prop :=
  ∀ st : RestatedState, st.2 ∉ st.1 → Mzk1Lemma24Target st.1 st.2

/-- Fixed measure: a pair (m,d) assigned to every state, compared lexicographically. -/
def RestatedMeasureLE (μ : RestatedState → Nat × Nat) (a b : RestatedState) : Prop :=
  lemma24Measure (μ a) (μ b)

/-- Base data for the corrected induction: at measure (0,0) (rational case) the restated
target holds (base provider to be supplied by hull's rational construction). -/
def RestatedBaseStatement (μ : RestatedState → Nat × Nat) : Prop :=
  ∀ st : RestatedState, μ st = (0, 0) → st.2 ∉ st.1 → Mzk1Lemma24Target st.1 st.2

/-- Step data for the corrected induction: at nonzero measure there is a next state of
strictly smaller lexicographic measure, a nonconstant q with CVInvariant on the current
set, q(beta) outside the Belyi target, and transport of the restated target from the next
state back to the current state (CV accounting via the composition law). -/
structure RestatedStep (μ : RestatedState → Nat × Nat) (st : RestatedState) where
  next : RestatedState
  decrease : lemma24Measure (μ next) (μ st)
  next_beta_avoid : next.2 ∉ next.1
  q : Polynomial ℚ
  cv_invariant : CVInvariant st.1 q
  beta_avoid : polyEvalP1 q st.2 ∉ specialSet ℚ
  transport : Mzk1Lemma24Target next.1 next.2 → Mzk1Lemma24Target st.1 st.2

/-- The step's CVInvariant gives the invariant fields directly (helper projection). -/
theorem s3135_RestatedStep_cvInvariant {μ : RestatedState → Nat × Nat} {st : RestatedState}
    (h : RestatedStep μ st) : CVInvariant st.1 h.q :=
  h.cv_invariant

/-- Corrected induction assembly STATEMENT (fixed μ): base data plus a step provider off
measure (0,0) implies the corrected conclusion.  This is the corrected 2.4 induction
target; no closure proof is claimed here (it is the statement the assembly will prove once
the base provider and step/CV accounting are supplied). -/
def RestatedInductionAssemblyStatement (μ : RestatedState → Nat × Nat) : Prop :=
  RestatedBaseStatement μ →
    (∀ st : RestatedState, μ st ≠ (0, 0) → st.2 ∉ st.1 → Nonempty (RestatedStep μ st)) →
      RestatedInductionConclusion

 /-- **(BASE, class-B named paper input)**: beta-avoiding rational Belyi map.  For
every finite rational point set S and rational beta outside S, a nonconstant q over Q
maps S into specialSet = {infinity,0,1}, keeps beta outside specialSet, and has all
critical values over C in {0,1}.  NOT available from current assets (TauCeti
Belyification controls q(S) and CV but NOT q(beta); polynomial post-composition keeping
{0,1} in itself cannot move q(beta) out).  Registered as the honest class-B paper input
of the corrected base case; hull attempts a proof in parallel. -/
def BetaAvoidingBelyiBaseInput : Prop :=
  ∀ (S : Finset (P1Point ℚ)) (β : P1Point ℚ), β ∉ S → Mzk1Lemma24Target S β

/-- **(STEP, named interface)**: step provider for the corrected induction at nonzero
measure: a next state of strictly smaller lexicographic measure together with a
nonconstant q satisfying CVInvariant on the current set, beta outside specialSet, and
transport of the restated target from the next state.  Registered as a named dependency
(step interface to be supplied by the f0/CV machinery and stage4). -/
def CorrectedStepProviderPaperInput (μ : RestatedState → Nat × Nat) : Prop :=
  ∀ st : RestatedState, μ st ≠ (0, 0) → st.2 ∉ st.1 → Nonempty (RestatedStep μ st)

/-- **(ASSEMBLY, named goal)**: the corrected induction assembly statement itself,
registered as the named assembly obligation (proof pending providers). -/
def CorrectedAssemblyPaperInput (μ : RestatedState → Nat × Nat) : Prop :=
  RestatedInductionAssemblyStatement μ

/-- Status: restated 2.4 induction/assembly statement filed with the corrected C-point
target vocabulary (specialSet / criticalValuesOverC / CVInvariant / CV composition law);
CV invariant composition is PROVED from the agreed composition-law statements.  Paper
obligation closure NOT claimed; binding HOLD. -/
def RestatedInductionStatus : Audit.Obligation :=
  { id := "MZK1.lemma24.restated-induction"
    source := "papers/motizuki_corpus/text/Noncritical Belyi Maps.txt Lemma 2.4 lines 144-206; Lead A280 restatement"
    status := Audit.VerificationStatus.interface
    note := "FILED (statement layer, fresh green): RestatedState, RestatedMeasureLE (fixed lexicographic measure), RestatedBaseStatement (measure 0 = rational case), RestatedStep (nonzero measure: next state, strict measure decrease, nonconstant q with CVInvariant on current set, q(beta) outside specialSet, target transport), RestatedInductionConclusion, RestatedInductionAssemblyStatement (base + step provider implies conclusion; no closure proof claimed). PROVED: s3135_polyEvalP1_comp and s3135_CVInvariant_comp (CV invariant preserved by composition, consuming CVCompositionLawStatement + SpecialSetPreservationStatement from RestatedLemma24InterfaceActual) and s3135_RestatedStep_cvInvariant. Vocabulary aligned with RestatedLemma24InterfaceActual / stage4 restated 2.2 (P1Point ℚ, specialSet, criticalValuesOverC). Reusable proved assets S1a/S1b/S2/S3/S2-i, F/G/D/M, L2.3, base provider remain available for the eventual assembly. No closure claim; binding HOLD; registry frozen 14041."
    dependsOn := [ "MZK1.lemma24.restated-target" ]
    sorryItems :=
      [ "proof of RestatedInductionAssemblyStatement (needs base provider + step provider/CV accounting + fixed-mu well-foundedness)",
        "stage4 CV composition law proof / integration",
        "re-derivation of measure decrease under the corrected target" ] }

#check s3135_CVInvariant_comp
#check RestatedInductionAssemblyStatement


/-- **Corrected finite-beta base input** (spec repair, stepxi A402): the beta-avoiding
rational Belyi base for FINITE beta = ofFinite b.  The unrestricted version
BetaAvoidingBelyiBaseInput is FALSE at beta = infinity because polyEvalP1 q infinity =
infinity is always in specialSet = {infinity,0,1}; hence the finite-beta restriction is
part of the corrected statement. -/
def BetaAvoidingBelyiBaseInputFinite : Prop :=
  ∀ (S : Finset (P1Point ℚ)) (b : ℚ), P1Point.ofFinite b ∉ S →
    Mzk1Lemma24Target S (P1Point.ofFinite b)

/-- The unrestricted beta-avoiding Belyi base input is FALSE: at S = empty and
beta = infinity the target's avoidance conjunct contradicts polyEvalP1 q infinity =
infinity in specialSet. -/
theorem s3135_betaAvoidingBelyiBase_false : ¬ BetaAvoidingBelyiBaseInput := by
  intro h
  obtain ⟨q, hdeg, hmap, havoid, hcv, hunr⟩ := h ∅ P1Point.infty (by simp)
  exact havoid (by simp [polyEvalP1, specialSet, P1Point.infty, P1Point.ofFinite])

/-- Corrected conditional base provider: the finite-beta input yields the restated target
for finite beta. -/
theorem s3135_target_of_betaAvoidingBelyiBaseFinite
    (h : BetaAvoidingBelyiBaseInputFinite) :
    ∀ (S : Finset (P1Point ℚ)) (b : ℚ), P1Point.ofFinite b ∉ S →
      Mzk1Lemma24Target S (P1Point.ofFinite b) :=
  h

/-- Spec-repair record (stepxi A402): the unrestricted base input is invalid at infinity;
the finite-beta restriction is the honest named input. -/
def BetaAvoidingBaseSpecRepair : Audit.Obligation :=
  { id := "MZK1.lemma24.beta-avoiding-spec-repair"
    source := "stepxi Mzk1Consumer24AdapterUnconditionalActual (A402); paper Lemma 2.4 F=Q component"
    status := Audit.VerificationStatus.interface
    note := "SPEC REPAIR: BetaAvoidingBelyiBaseInput (unrestricted over P1(Q)) is FALSE — infinity-beta counterexample proved here (s3135_betaAvoidingBelyiBase_false): polyEvalP1 q infinity = infinity is always in specialSet, so the avoidance conjunct fails for beta = infinity. The corrected named input is BetaAvoidingBelyiBaseInputFinite (finite beta = ofFinite b), matching stepxi H24BaseConcreteFinite. Conditional theorems that consumed the unrestricted input are superseded by the finite-beta versions; no closure claim; binding HOLD; registry frozen 14041."
    dependsOn := [ "MZK1.lemma24.rational-input-scope" ]
    sorryItems := [ "BetaAvoidingBelyiBaseInputFinite (class-B named, finite beta)" ] }
/-- SCOPE note (Lead A313/A314): the restated induction in this file is the rational-input
F = Q component ONLY (fixed lexicographic measure on rational point sets, base m(S)=0,
rational Belyi existence).  The paper-scope algebraic nested induction on (m(S), d(S))
over S subset P^1(Qbar) is registered as the named class-B input
AlgebraicNestedInductionInput (PaperScopeLemma24Actual).  This is NOT full Lemma 2.4; no
closure claim.  Coverage: F = Q component delivered, full-Qbar reduction named (not
complete). -/
def ScopeNoteFQComponent : Audit.Obligation :=
  { id := "MZK1.lemma24.induction.scope-note"
    source := "Lead A313/A314 scope decision; papers/motizuki_corpus/text/Noncritical Belyi Maps.txt Lemma 2.4 lines 163-206"
    status := Audit.VerificationStatus.interface
    note := "SCOPE: rational-input F=Q component only. Named class-B inputs remain BetaAvoidingBelyiBaseInput, CorrectedStepProviderPaperInput, CorrectedAssemblyPaperInput, plus AlgebraicNestedInductionInput (paper 163-206 algebraic nested (m,d) induction). No closure claim; binding HOLD; gate NOT PASSED; registry frozen 14041."
    dependsOn := [ "MZK1.lemma24.paper-scope", "MZK1.lemma24.rational-input-scope" ]
    sorryItems := [ "paper-scope algebraic nested induction (named AlgebraicNestedInductionInput)" ] }

end LeanFormal.IUT.XiFPaper.RestatedLemma24InductionActual
end
-- scope-note-compile-bump