import tmp.sheaf.xif.paper.Mzk1Lemma22CompositionActual
import Mathlib.Tactic

/-! # Mzk1Lemma22InductionActual — [Mzk1] Lemma 2.2 (c): strong induction on |S| + base

STEP 0 prior-art: corpus Lemma 2.2 lines 106-135 (induct on |S|, compose morphisms);
Mzk1Lemma22CompositionActual (CITABLE: composition laws, Mzk1Lemma22InductionStep,
mzk1Lemma22_comp_witness); Mzk1P1MorphismInterfaceActual.  The constructive step is
routed to stepxi (Mzk1Lemma22StepConstructionActual); this file proves the cardinal
induction consuming it.  No fake: partial shape only (nonconstant + preserves + avoids);
unramifiedness recorded as obligation (needs polynomial chain rule layer). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma22InductionActual

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22CompositionActual

universe u
variable {K : Type u} [Field K] [DecidableEq K]

/-- Partial Lemma 2.2 shape: nonconstant map preserving S into the target and avoiding
beta (unramifiedness deliberately excluded). -/
def Mzk1Lemma22PartialShape (S : Finset (P1Point K)) (β : P1Point K) (C : ℝ)
    (finalTarget : Set (P1Point K)) : Prop :=
  ∃ φ : P1Morphism K, φ.nonconstant ∧
    PreservesSet φ (↑S : Set (P1Point K)) finalTarget ∧
    AvoidsPoint φ β finalTarget

/-- A full Lemma 2.2 statement shape gives the partial shape. -/
theorem partial_of_shape {S : Finset (P1Point K)} {β : P1Point K} {C : ℝ}
    {finalTarget : Set (P1Point K)} {u : P1Point K → Prop}
    (h : Mzk1Lemma22StatementShape K S β C finalTarget u) :
    Mzk1Lemma22PartialShape (K := K) S β C finalTarget := by
  obtain ⟨φ, hnc, hpres, hav, _hunr⟩ := h
  exact ⟨φ, hnc, hpres, hav⟩

/-- One-step composition for the partial shape. -/
theorem comp_partial (st : Mzk1Lemma22InductionStep K) {C : ℝ}
    (finalTarget : Set (P1Point K))
    (htarget : st.targetSet = (↑st.targetS : Set (P1Point K)))
    (hψ : Mzk1Lemma22PartialShape (K := K) st.targetS st.beta' C finalTarget) :
    Mzk1Lemma22PartialShape (K := K) st.source st.beta C finalTarget := by
  obtain ⟨ψ, hnc, hpres, hav⟩ := hψ
  refine ⟨Mzk1Lemma22CompositionActual.comp st.phi ψ hnc, hnc, ?_, ?_⟩
  · have hpres' : PreservesSet ψ st.targetSet finalTarget := by
      rw [htarget]
      exact hpres
    exact PreservesSet_comp st.preserves hpres' hnc
  · show ψ.mapPoints (st.phi.mapPoints st.beta) ∉ finalTarget
    rw [← st.beta'_eq]
    exact hav

/-- Strong induction on |S|: base case (|S| <= 3) and step-existence imply the partial
Lemma 2.2 shape for every pair (S,beta).

DEPRECATED as a final path (A280/A281 integrity review): base and stepExists here are
quantified over ALL pairs (S,beta), which is unsatisfiable for beta in S and loses the
information "phi = gPoly and Lemma22Hypotheses holds on the image".  Do NOT use this
theorem to derive the paper's Lemma 2.2; use Mzk1Lemma22StepInterfaceQActual (explicit
phi = gPoly + H-on-image) and the flat Good induction in RestatedLemma22TargetActual.
Kept only as a generic cardinal-induction skeleton for reference. -/
theorem mzk1Lemma22_partial_induction {C : ℝ} (finalTarget : Set (P1Point K))
    (base : ∀ (S : Finset (P1Point K)) (β : P1Point K),
      S.card ≤ 3 → Mzk1Lemma22PartialShape (K := K) S β C finalTarget)
    (stepExists : ∀ (S : Finset (P1Point K)) (β : P1Point K), 3 < S.card →
      ∃ st : Mzk1Lemma22InductionStep K, st.source = S ∧ st.beta = β ∧
        st.targetSet = (↑st.targetS : Set (P1Point K))) :
    ∀ (S : Finset (P1Point K)) (β : P1Point K),
      Mzk1Lemma22PartialShape (K := K) S β C finalTarget := by
  have main : ∀ n (S : Finset (P1Point K)), S.card = n → ∀ β : P1Point K,
      Mzk1Lemma22PartialShape (K := K) S β C finalTarget := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S hcard β
      by_cases hsmall : S.card ≤ 3
      · exact base S β hsmall
      · have hbig : 3 < S.card := Nat.lt_of_not_ge hsmall
        obtain ⟨st, hsrc, hbeta, htarget⟩ := stepExists S β hbig
        have hlt : st.targetS.card < n := by
          rw [← hcard, ← hsrc]
          exact st.card_lt
        have hIH := ih st.targetS.card hlt st.targetS rfl st.beta'
        have hcomp := comp_partial st finalTarget htarget hIH
        simpa [← hsrc, ← hbeta] using hcomp
  intro S β
  exact main S.card S rfl β

#check Mzk1Lemma22PartialShape
#check partial_of_shape
#check comp_partial
#check mzk1Lemma22_partial_induction

end LeanFormal.IUT.XiFPaper.Mzk1Lemma22InductionActual
end

-- touch for fresh olean (checker OLEAN_STALE)
