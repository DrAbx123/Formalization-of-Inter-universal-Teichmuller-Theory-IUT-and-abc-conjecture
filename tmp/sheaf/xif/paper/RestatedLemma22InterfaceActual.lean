import tmp.sheaf.xif.paper.RestatedLemma24InterfaceActual
import tmp.sheaf.xif.paper.Mzk1GChoiceScaleActual
import tmp.sheaf.xif.paper.Mzk1Lemma22StatementShapeActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# RestatedLemma22InterfaceActual — RESTATED [Mzk1] Lemma 2.2 interface/statement (SINGLE SOURCE)

STEP 0 prior-art (reuse, no re-proof): vocabulary unified with abc's
RestatedLemma24InterfaceActual (CITABLE): P1Point ℚ, specialSet (K), polyEvalP1,
criticalValuesOverC (Set ℂ), CVCompositionLawStatement, SpecialSetPreservationStatement;
Mzk1GChoiceScaleActual.Lemma22Hypotheses (paper conditions); Mzk1Lemma22StatementShapeActual
(old polynomial-level Mzk1Lemma22FullShape, Q-point unramified version) for the bridge
record; corpus [Mzk1] Lemma 2.2 lines 106-135.

RESTATEMENT (Lead A288, C-point version): the target is over P1(Q) with the fixed Belyi
target set {infinity,0,1} and the C-point critical-value condition (paper Lemma 2.1(b)
is over C, not only Q).  This file is the SINGLE SOURCE for stage4's induction proof:
stage4 imports it and proves Mzk1Lemma22InductionStatement; the bridge to the old
Mzk1Lemma22FullShape is recorded as a statement (needs the C->Q restriction; provable
with the aeval/eval cast lemmas).

NO closure claim; gate NOT PASSED; h22 binding remains HOLD/history-only.
Registry frozen 14041; no registry edits.  No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.RestatedLemma22InterfaceActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceScaleActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22StatementShapeActual

/-- **Restated [Mzk1] Lemma 2.2 target (C-point version):** there is a nonconstant
polynomial f over Q carrying S into the fixed Belyi set {infinity,0,1} inside P1(Q),
carrying beta outside it, and satisfying the C-point critical-value condition: if a
complex value of f is not 0 or 1, then the derivative does not vanish there. -/
def Mzk1Lemma22Target (S : Finset (P1Point ℚ)) (β : P1Point ℚ) : Prop :=
  ∃ f : Polynomial ℚ,
    1 ≤ f.natDegree ∧
    (∀ p ∈ S, polyEvalP1 f p ∈ specialSet ℚ) ∧
    polyEvalP1 f β ∉ specialSet ℚ ∧
    (∀ z : ℂ, Polynomial.aeval z f ∉ ({0, 1} : Set ℂ) →
      Polynomial.aeval z (Polynomial.derivative f) ≠ 0)

/-- **Flat Good predicate** (the induction invariant): the four components of the
restated 2.2 target in flat form (b). -/
def Good (f : Polynomial ℚ) (S : Finset (P1Point ℚ)) (β : P1Point ℚ) : Prop :=
  1 ≤ f.natDegree ∧
  (∀ p ∈ S, polyEvalP1 f p ∈ specialSet ℚ) ∧
  polyEvalP1 f β ∉ specialSet ℚ ∧
  (∀ z : ℂ, Polynomial.aeval z f ∉ ({0, 1} : Set ℂ) →
    Polynomial.aeval z (Polynomial.derivative f) ≠ 0)

/-- The target is exactly the existential of Good. -/
theorem Mzk1Lemma22Target_iff_exists_Good (S : Finset (P1Point ℚ)) (β : P1Point ℚ) :
    Mzk1Lemma22Target S β ↔ ∃ f : Polynomial ℚ, Good f S β := by
  constructor
  · rintro ⟨f, hdeg, hpres, hav, hcrit⟩
    exact ⟨f, hdeg, hpres, hav, hcrit⟩
  · rintro ⟨f, hdeg, hpres, hav, hcrit⟩
    exact ⟨f, hdeg, hpres, hav, hcrit⟩

/-- **(c) Restated induction statement:** for every cardinal bound n, every finite
S with card <= n and every beta satisfying the paper hypotheses, there is a Good
polynomial.  Measure = cardinality bound n; beta is inside the quantifier. -/
def Mzk1Lemma22InductionStatement : Prop :=
  ∀ (n : Nat) (S : Finset (P1Point ℚ)) (β : P1Point ℚ),
    S.card ≤ n → Lemma22Hypotheses S β → ∃ f : Polynomial ℚ, Good f S β

/-- The induction statement implies the target (the real consumer direction). -/
theorem target_of_induction (h : Mzk1Lemma22InductionStatement)
    (S : Finset (P1Point ℚ)) (β : P1Point ℚ) (H : Lemma22Hypotheses S β) :
    Mzk1Lemma22Target S β := by
  obtain ⟨f, hf⟩ := h S.card S β le_rfl H
  exact (Mzk1Lemma22Target_iff_exists_Good S β).mpr ⟨f, hf⟩

/-- Vocabulary-alignment record with abc's RestatedLemma24InterfaceActual: the CV
composition law and special-set preservation used by the nested induction are exactly
abc's statements (single definition source, no duplication). -/
def Mzk1Lemma22CVCompat : Prop :=
  CVCompositionLawStatement ∧ SpecialSetPreservationStatement

/-- Bridge record: the restated C-point target implies the old (Q-point) polynomial
FullShape once the C->Q restriction of the derivative condition is formalized.
Recorded as a statement (not proved here; the C->Q transport uses aeval/eval casts). -/
def Mzk1Lemma22TargetImpliesFullShape : Prop :=
  ∀ (S : Finset (P1Point ℚ)) (β : P1Point ℚ),
    Mzk1Lemma22Target S β → Mzk1Lemma22FullShape S β

/-- Interface rows: (component, evidence/vocabulary, status). -/
def restatedLemma22Rows : List (String × String × String) :=
  [ ("restated target (C-point, P1(Q), specialSet {inf,0,1})", "Mzk1Lemma22Target", "DEFINED (statement)"),
    ("flat Good predicate", "Good", "DEFINED (statement)"),
    ("target = exists Good", "Mzk1Lemma22Target_iff_exists_Good", "PROVED (rfl-level)"),
    ("induction statement (fixed cardinal measure)", "Mzk1Lemma22InductionStatement", "DEFINED (statement)"),
    ("induction => target", "target_of_induction", "PROVED"),
    ("vocabulary alignment with restated 2.4", "Mzk1Lemma22CVCompat = CVCompositionLawStatement ∧ SpecialSetPreservationStatement (imported from RestatedLemma24InterfaceActual)", "SHARED SINGLE SOURCE"),
    ("bridge target => old FullShape (C->Q restriction)", "Mzk1Lemma22TargetImpliesFullShape", "STATEMENT ONLY (TODO for gated wiring)") ]

theorem restatedLemma22Rows_length : restatedLemma22Rows.length = 7 := rfl


/-- Explicit SCOPE record (Lead A311/A313): the rational-input restated 2.2
target is the F=Q BASE-ONLY component (base case m(S)=0 + rational Belyi existence).
The paper's algebraic P1(Qbar) inputs are NOT modeled at this layer; the full-Qbar
reduction is NAMED (not complete): (D) finite-Galois descent PROVED, infinite fixed field
class-B named, 2.3 Moebius separation over Qbar/C, and the algebraic nested induction
(paper 179-206) recorded as AlgebraicNestedInductionInput. -/
def restatedLemma22Scope : List (String × String) :=
  [ ("input scope", "F=Q BASE-ONLY: S : Finset (P1Point Q), beta : P1Point Q (rational points only); base case m(S)=0 + rational Belyi existence"),
    ("paper scope", "paper Lemma 2.2/2.4 inputs live over P1(Qbar): S algebraic, beta in Qbar minus S; NOT modeled at this interface layer"),
    ("coverage (AMENDED canonical line)", "F=Q conditional wiring delivered (named beta-avoiding Belyi base input) + full-Qbar reduction named (not complete)"),
    ("reduction layers (named)", "(D) finite-Galois descent PROVED; infinite fixed field class-B named; 2.3 Moebius separation over Qbar/C; algebraic nested induction (paper 179-206) = AlgebraicNestedInductionInput"),
    ("consequence", "rational inputs: measure m/d trivial; no closure claim") ]

theorem restatedLemma22Scope_length : restatedLemma22Scope.length = 5 := rfl

/-- Polynomial action on P1 over the algebraic closure (statement interface only). -/
def polyEvalP1AC (q : Polynomial (AlgebraicClosure ℚ)) :
    P1Point (AlgebraicClosure ℚ) → P1Point (AlgebraicClosure ℚ) :=
  fun p => p.map (fun x => q.eval x)

/-- **AlgebraicNestedInductionInput** (paper lines 179-206, m/d step; NAMED class-B input,
statement only): for algebraic S and beta outside S there is a nonconstant polynomial f
over Qbar mapping S into the fixed Belyi target, beta outside it, and whose critical
values are rational (contained in some rational set S_phi).  This is the paper-scope
input needed by the full-Qbar reduction; it is NOT proved here and NOT assumed true. -/
def AlgebraicNestedInductionInput : Prop :=
  ∀ (S : Finset (P1Point (AlgebraicClosure ℚ)))
      (β : P1Point (AlgebraicClosure ℚ)),
    β ∉ S →
      ∃ (Sphi : Finset ℚ) (f : Polynomial (AlgebraicClosure ℚ)),
        0 < f.natDegree ∧
        (∀ p ∈ S, polyEvalP1AC f p ∈ specialSet (AlgebraicClosure ℚ)) ∧
        polyEvalP1AC f β ∉ specialSet (AlgebraicClosure ℚ) ∧
        (∀ z : AlgebraicClosure ℚ,
          Polynomial.aeval z (Polynomial.derivative f) = 0 →
            ∃ r : ℚ, r ∈ Sphi ∧
              Polynomial.aeval z f = algebraMap ℚ (AlgebraicClosure ℚ) r)

end LeanFormal.IUT.XiFPaper.RestatedLemma22InterfaceActual

end
