import Mathlib
import tmp.sheaf.xif.paper.Mzk1P1MorphismInterfaceActual
import LeanFormal.IUT.Audit.Status

noncomputable section

namespace LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual

/-- The Belyi target set {infinity, 0, 1} inside P^1(K). -/
def specialSet (K : Type) [Zero K] [One K] : Set (P1Point K) :=
  {(P1Point.infty : P1Point K), P1Point.ofFinite (0 : K), P1Point.ofFinite (1 : K)}

/-- Evaluation of a rational polynomial q on P^1(Q), with q(infinity) = infinity. -/
def polyEvalP1 (q : Polynomial ℚ) : P1Point ℚ → P1Point ℚ :=
  fun p => p.map (fun x => Polynomial.eval x q)

/-- Critical values of q over C at finite points: the values q(z) at roots z of q'. -/
def criticalValuesOverC (q : Polynomial ℚ) : Set ℂ :=
  {c : ℂ | ∃ z : ℂ, ¬q.natDegree = 0 ∧
    Polynomial.aeval z (Polynomial.derivative q) = 0 ∧ Polynomial.aeval z q = c}

/-- **[Restated Lemma 2.4 target]** (Lead A280, C-point version): there is a
nonconstant polynomial q over Q such that q carries S into the fixed Belyi target set
{infinity, 0, 1} (as points of P^1(Q)), carries beta outside it, and all critical values
of q over C lie in {0,1} (equivalently: q is unramified away from {0,1,infinity}). -/
def Mzk1Lemma24Target (S : Finset (P1Point ℚ)) (β : P1Point ℚ) : Prop :=
  ∃ q : Polynomial ℚ,
    0 < q.natDegree ∧
    (∀ p ∈ S, polyEvalP1 q p ∈ specialSet ℚ) ∧
    polyEvalP1 q β ∉ specialSet ℚ ∧
    criticalValuesOverC q ⊆ ({0, 1} : Set ℂ) ∧
    (∀ z : ℂ, Polynomial.aeval z q ∉ ({0, 1} : Set ℂ) →
      Polynomial.aeval z (Polynomial.derivative q) ≠ 0)

/-- The induction invariant carried by the restated nested induction: q maps the
current finite set into the Belyi target and q is unramified away from {0,1}. -/
def CVInvariant (S : Finset (P1Point ℚ)) (q : Polynomial ℚ) : Prop :=
  0 < q.natDegree ∧
    (∀ p ∈ S, polyEvalP1 q p ∈ specialSet ℚ) ∧
    criticalValuesOverC q ⊆ ({0, 1} : Set ℂ)

/-- Corrected Lemma 2.4 statement shape (restated target; no old interface predicates). -/
def Mzk1Lemma24CorrectedStatement : Prop :=
  ∀ (S : Finset (P1Point ℚ)) (β : P1Point ℚ), β ∉ S → Mzk1Lemma24Target S β

/-- CV composition law statement (to be proved by hull's CV file): critical values of a
composite are contained in the image of the first factor's critical values together with
the second factor's critical values. -/
def CVCompositionLawStatement : Prop :=
  ∀ q r : Polynomial ℚ, criticalValuesOverC (r.comp q) ⊆
    (fun c => Polynomial.aeval c r) '' (criticalValuesOverC q) ∪ criticalValuesOverC r

/-- Belyi special-set preservation under composition (second factor keeps {0,1} in
itself), the companion of the CV composition law. -/
def SpecialSetPreservationStatement : Prop :=
  ∀ r : Polynomial ℚ,
    Polynomial.aeval (0 : ℂ) r ∈ ({0, 1} : Set ℂ) →
    Polynomial.aeval (1 : ℂ) r ∈ ({0, 1} : Set ℂ) →
      ∀ c : ℂ, c ∈ ({0, 1} : Set ℂ) → Polynomial.aeval c r ∈ ({0, 1} : Set ℂ)

/-- Audit record: relation to the old (degenerate) interface goal.  The restated target
above does NOT use Mzk1Lemma24StatementShape; the old goal (and StepProvider/BaseProvider
statements built on it) was equivalent to the trivial condition beta notin S and cannot
carry the paper obligation.  Reusable proved assets remain: S1a/S1b/S2/S3/S2-i, F/G/D/M
evidence, L2.3 normalization + transfer, rational base provider. -/
def RestatedTargetRelationRecord : Audit.Obligation :=
  { id := "MZK1.lemma24.restated-target"
    source := "papers/motizuki_corpus/text/Noncritical Belyi Maps.txt Lemma 2.4 lines 144-160; Lead A277-A281 restatement"
    status := Audit.VerificationStatus.interface
    note := "RESTATED TARGET (this file, does not reference the old degenerate goal): q in Q[X] nonconstant; q maps S into specialSet = {infinity,0,1} inside P^1(Q); q(beta) outside specialSet; critical values of q over C lie in {0,1}; q unramified away from {0,1} (C-point condition). Vocabulary unified with stage4: P1Point Q (P^1(Q)) and CV as Set (P1Point C) values via C-point evaluation; specialSet is the fixed Belyi target {0,1,infinity} (no arbitrary rational S_phi). Induction invariant: CVInvariant (S, q) with fixed measure mu; composition law statement CV(psi o phi) = psi(CV phi) union CV psi formalized as CVCompositionLawStatement plus SpecialSetPreservationStatement (psi keeps {0,1}). OLD GOAL DEGENERACY recorded separately (StepProvider/BaseProvider statements built on the old interface are vacuous: witness mapPoints:=id, ratFunc:=0, T:=S, unramifiedAt:=complement T satisfies shape iff beta notin S). Paper obligation closure NOT claimed; binding HOLD; registry frozen 14041."
    dependsOn := [ "MZK1.lemma24.assembly" ]
    sorryItems :=
      [ "proof of Mzk1Lemma24CorrectedStatement under the restated target (nested induction with CV invariant and fixed mu)",
        "CVCompositionLawStatement (hull)",
        "SpecialSetPreservationStatement",
        "integration with stage4 flat Good target / specialSet vocabulary" ] }

#check Mzk1Lemma24Target
#check CVCompositionLawStatement

/-- SCOPE note (Lead A313/A314, explicit scope split): the P^1(Q)-typed target in this
file is the rational-input F = Q component ONLY (base case m(S) = 0 plus rational Belyi
existence).  The paper-scope [Mzk1] Lemma 2.4 (S subset P^1(Qbar), beta in Qbar minus S,
S_phi subset P^1(Q), phi defined over the field of definition) is a NAMED reduction layer
(PaperScopeLemma24Actual + AlgebraicNestedInductionInput + descent/2.3/2.2 inputs).  This
is NOT full Lemma 2.4 and no closure is claimed.  Coverage: F = Q component delivered,
full-Qbar reduction named (not complete). -/
def ScopeNoteFQComponent : Audit.Obligation :=
  { id := "MZK1.lemma24.interface.scope-note"
    source := "Lead A313/A314 scope decision; papers/motizuki_corpus/text/Noncritical Belyi Maps.txt Lemma 2.4 lines 144-160"
    status := Audit.VerificationStatus.interface
    note := "SCOPE: rational-input F=Q component only (base m(S)=0 + rational Belyi existence). Paper-scope algebraic layer is named (PaperScopeLemma24Actual, AlgebraicNestedInductionInput, descent finite-Galois PROVED + infinite fixed-field class-B, 2.3 separation, 2.2 Qbar target). NOT full Lemma 2.4; no closure claim; binding HOLD; gate NOT PASSED; registry frozen 14041."
    dependsOn := [ "MZK1.lemma24.paper-scope" ]
    sorryItems := [ "paper-scope algebraic layer (named)" ] }

end LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual
end