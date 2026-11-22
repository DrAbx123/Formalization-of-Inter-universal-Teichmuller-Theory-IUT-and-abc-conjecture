import tmp.sheaf.xif.paper.RestatedLemma22InterfaceActual
import tmp.sheaf.xif.paper.Mzk1Lemma22CritValueActual
import Mathlib.Tactic

/-!
# Mzk1TargetImpliesFullShapeActual — bridge: restated [Mzk1] 2.2 target ⇒ old FullShape

STEP 0 prior-art (reuse, no re-proof):
* RestatedLemma22InterfaceActual.Mzk1Lemma22Target / Good — the restated 2.2 target
  (C-point critical-value condition; S β : P1Point ℚ; target set specialSet ℚ);
* Mzk1Lemma22StatementShapeActual.Mzk1Lemma22FullShape — the old polynomial-level full
  shape consumed by the Thm 2.5 / GenEll wiring
  (∃ f, 1 ≤ f.natDegree, PreservesSet, AvoidsPoint, UnramifiedOver);
* Mzk1PolyMapActual.polyMorphism / polyMapPoints / polyUnramifiedAt / specialSet —
  the real polynomial P¹ construction: finite x ↦ f x, ∞ ↦ ∞, unramified at a
  finite point iff the derivative does not vanish there;
* Mzk1Lemma22CritValueActual.aeval_cast_eval (PROVED: aeval of a ℚ-polynomial at a
  cast rational equals the cast of its eval).

THIS FILE proves the C-point → Q-point restriction required by the bridge:

  Mzk1Lemma22Target S β → Mzk1Lemma22FullShape S β.

Field-by-field (obtain ⟨f, hdeg, hpres, hβ, hcrit⟩ from the target):
* PreservesSet and AvoidsPoint are pure vocabulary transport:
  polyEvalP1 f p = polyMapPoints f p (polyEvalP1_eq_polyMapPoints) and the two
  spellings of the Belyi target set agree (mem_specialSet_iff);
* UnramifiedOver: at ∞ the premise is false because ∞ ∈ specialSet;
  at a finite point x with some (f x) ∉ specialSet we get f x ∉ {0,1} in ℚ, hence
  aeval (x:ℂ) f ∉ {0,1}, hence aeval (x:ℂ) f' ≠ 0 by the target's C-point condition,
  hence f'(x) ≠ 0 by aeval_cast_eval and injectivity of ℚ ↪ ℂ (Rat.cast_inj).

Consequences for consumers: mzk1Lemma22TargetImpliesFullShape proves the bridge record
RestatedLemma22InterfaceActual.Mzk1Lemma22TargetImpliesFullShape, and
fullShape_of_induction composes with stage4's target_of_induction so that a proved
2.2 induction statement plus the paper hypotheses Lemma22Hypotheses yields a
Mzk1Lemma22FullShape directly (the shape the GenEll / Thm 2.5 wiring consumes).

HONESTY: this is a conditional implication only (it does not prove the 2.2 target
itself). No sorry/axiom/True/PUnit/toy carrier; axiom set ⊆
{propext, Classical.choice, Quot.sound}. Registry frozen 14041; no registry edits.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1TargetImpliesFullShapeActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual

/-- The two spellings of the Belyi target set {∞, 0, 1} agree: the polynomial-map
layer Mzk1PolyMapActual.specialSet (a set comprehension) and the restated-interface
layer RestatedLemma24InterfaceActual.specialSet ℚ (a set literal). -/
theorem mem_specialSet_iff (p : P1Point ℚ) :
    p ∈ LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual.specialSet ↔
      p ∈ LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual.specialSet ℚ := by
  rcases p with _ | x <;>
    simp [LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual.specialSet,
      LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual.specialSet]

/-- The restated-interface evaluation polyEvalP1 and the polynomial-map layer
polyMapPoints are the same map on P¹(ℚ) (Option.map vs. pattern matching). -/
theorem polyEvalP1_eq_polyMapPoints (f : ℚ[X]) (p : P1Point ℚ) :
    LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual.polyEvalP1 f p =
      LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual.polyMapPoints f p := by
  rcases p with _ | x <;> rfl

/-- Membership criterion for the image of a finite point: some (f x) is special
({∞,0,1}) iff f x is 0 or 1 (the image of a finite point is never ∞). -/
theorem polyMapPoints_some_mem_iff (f : ℚ[X]) (x : ℚ) :
    LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual.polyMapPoints f (some x) ∈
        LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual.specialSet ↔
      (f.eval x = 0 ∨ f.eval x = 1) := by
  change (some (f.eval x) : P1Point ℚ) ∈
    LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual.specialSet ↔ (f.eval x = 0 ∨ f.eval x = 1)
  simp [LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual.specialSet,
    LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual.P1Point.infty,
    LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual.P1Point.ofFinite]

/-- At a finite point with non-special value, the polynomial map is unramified:
the Q-point derivative test, derived from the target's C-point critical-value
condition by the aeval/eval cast bridge. -/
theorem derivative_eval_ne_zero_of_not_mem_specialSet
    (f : ℚ[X]) (x : ℚ)
    (hcrit : ∀ z : ℂ, Polynomial.aeval z f ∉ ({0, 1} : Set ℂ) →
      Polynomial.aeval z (Polynomial.derivative f) ≠ 0)
    (hx : LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual.polyMapPoints f (some x) ∉
      LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual.specialSet) :
    f.derivative.eval x ≠ 0 := by
  -- hx says f x is neither 0 nor 1 as a rational number.
  have hx' : ¬ (f.eval x = 0 ∨ f.eval x = 1) :=
    fun h => hx ((polyMapPoints_some_mem_iff f x).mpr h)
  -- Lift to ℂ: the value at the cast point is still outside {0,1}.
  have hC : Polynomial.aeval ((x : ℚ) : ℂ) f ∉ ({0, 1} : Set ℂ) := by
    rw [LeanFormal.IUT.XiFPaper.Mzk1Lemma22CritValueActual.aeval_cast_eval]
    intro hmem
    have hmem' : ((f.eval x : ℚ) : ℂ) = 0 ∨ ((f.eval x : ℚ) : ℂ) = 1 := by
      simpa using hmem
    rcases hmem' with h0 | h1
    · refine hx' (Or.inl ?_)
      have h0' : ((f.eval x : ℚ) : ℂ) = ((0 : ℚ) : ℂ) := by
        rw [Rat.cast_zero]
        exact h0
      exact Rat.cast_inj.mp h0'
    · refine hx' (Or.inr ?_)
      have h1' : ((f.eval x : ℚ) : ℂ) = ((1 : ℚ) : ℂ) := by
        rw [Rat.cast_one]
        exact h1
      exact Rat.cast_inj.mp h1'
  -- Apply the target's C-point critical-value condition at z = x.
  have hcrit' := hcrit ((x : ℚ) : ℂ) hC
  rw [LeanFormal.IUT.XiFPaper.Mzk1Lemma22CritValueActual.aeval_cast_eval] at hcrit'
  intro hzero
  apply hcrit'
  rw [hzero]
  simp

/-- MAIN BRIDGE: the restated [Mzk1] Lemma 2.2 target (C-point critical-value
condition, target set {∞,0,1}) implies the old polynomial-level Mzk1Lemma22FullShape
(PreservesSet + AvoidsPoint + UnramifiedOver with the rational derivative test). -/
theorem Mzk1Lemma22Target_to_fullShape (S : Finset (P1Point ℚ)) (β : P1Point ℚ)
    (h : LeanFormal.IUT.XiFPaper.RestatedLemma22InterfaceActual.Mzk1Lemma22Target S β) :
    LeanFormal.IUT.XiFPaper.Mzk1Lemma22StatementShapeActual.Mzk1Lemma22FullShape S β := by
  obtain ⟨f, hdeg, hpres, hβ, hcrit⟩ := h
  refine ⟨f, hdeg, ?_, ?_, ?_⟩
  · -- PreservesSet: transport polyEvalP1 membership to polyMapPoints membership.
    intro p hp
    have h1 : LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual.polyEvalP1 f p ∈
        LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual.specialSet ℚ := hpres p hp
    rw [polyEvalP1_eq_polyMapPoints] at h1
    exact (mem_specialSet_iff (LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual.polyMapPoints f p)).mpr h1
  · -- AvoidsPoint: the same transport in the contrapositive direction.
    intro hcon
    apply hβ
    have h' : LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual.polyMapPoints f β ∈
        LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual.specialSet := hcon
    rw [polyEvalP1_eq_polyMapPoints]
    exact (mem_specialSet_iff (LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual.polyMapPoints f β)).mp h'
  · -- UnramifiedOver {p | p ∉ specialSet} (polyUnramifiedAt f).
    intro p hp
    rcases p with _ | x
    · -- At infinity the premise is impossible: ∞ is a special (target) value.
      exact absurd LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual.infty_mem_specialSet hp
    · -- At a finite point this is exactly the Q-point derivative test.
      exact derivative_eval_ne_zero_of_not_mem_specialSet f x hcrit hp

/-- The bridge record RestatedLemma22InterfaceActual.Mzk1Lemma22TargetImpliesFullShape
(named there as STATEMENT ONLY) is PROVED here. -/
theorem mzk1Lemma22TargetImpliesFullShape :
    LeanFormal.IUT.XiFPaper.RestatedLemma22InterfaceActual.Mzk1Lemma22TargetImpliesFullShape :=
  fun S β h => Mzk1Lemma22Target_to_fullShape S β h

/-- Per-witness form of the bridge: a single Good polynomial already yields the full
shape (useful for consumers that hold a witness instead of the existential target). -/
theorem fullShape_of_good (S : Finset (P1Point ℚ)) (β : P1Point ℚ) (f : ℚ[X])
    (hf : LeanFormal.IUT.XiFPaper.RestatedLemma22InterfaceActual.Good f S β) :
    LeanFormal.IUT.XiFPaper.Mzk1Lemma22StatementShapeActual.Mzk1Lemma22FullShape S β :=
  Mzk1Lemma22Target_to_fullShape S β
    ((LeanFormal.IUT.XiFPaper.RestatedLemma22InterfaceActual.Mzk1Lemma22Target_iff_exists_Good
      S β).mpr ⟨f, hf⟩)

/-- Consumer form: a proved restated-2.2 induction statement together with the paper
hypotheses Lemma22Hypotheses gives the old Mzk1Lemma22FullShape directly
(composition of stage4's target_of_induction with this file's main bridge). -/
theorem fullShape_of_induction
    (h : LeanFormal.IUT.XiFPaper.RestatedLemma22InterfaceActual.Mzk1Lemma22InductionStatement)
    (S : Finset (P1Point ℚ)) (β : P1Point ℚ)
    (H : LeanFormal.IUT.XiFPaper.Mzk1GChoiceScaleActual.Lemma22Hypotheses S β) :
    LeanFormal.IUT.XiFPaper.Mzk1Lemma22StatementShapeActual.Mzk1Lemma22FullShape S β :=
  Mzk1Lemma22Target_to_fullShape S β
    (LeanFormal.IUT.XiFPaper.RestatedLemma22InterfaceActual.target_of_induction h S β H)

/-- Provenance/status rows for the bridge (item, evidence, status). -/
def targetImpliesFullShapeRows : List (String × String × String) :=
  [ ("target set vocabulary: Mzk1PolyMapActual.specialSet vs RestatedLemma24InterfaceActual.specialSet",
      "mem_specialSet_iff", "PROVED"),
    ("evaluation vocabulary: polyEvalP1 vs polyMapPoints",
      "polyEvalP1_eq_polyMapPoints", "PROVED"),
    ("finite image point is special iff its value is 0 or 1",
      "polyMapPoints_some_mem_iff", "PROVED"),
    ("C-point CV condition ⇒ Q-point derivative test at a finite non-special value",
      "derivative_eval_ne_zero_of_not_mem_specialSet (aeval_cast_eval + Rat.cast_inj)", "PROVED"),
    ("restated 2.2 target ⇒ old FullShape",
      "Mzk1Lemma22Target_to_fullShape", "PROVED"),
    ("bridge record Mzk1Lemma22TargetImpliesFullShape (named TODO in RestatedLemma22InterfaceActual)",
      "mzk1Lemma22TargetImpliesFullShape", "PROVED (discharges the named TODO)"),
    ("induction statement + Lemma22Hypotheses ⇒ FullShape (consumer form)",
      "fullShape_of_induction (target_of_induction ∘ main bridge)", "PROVED (conditional on the induction statement)"),
    ("per-witness form from Good",
      "fullShape_of_good", "PROVED"),
    ("proof of Mzk1Lemma22InductionStatement itself",
      "stage4 nested induction (not in this file)", "OUT OF SCOPE / unchanged") ]

theorem targetImpliesFullShapeRows_length : targetImpliesFullShapeRows.length = 9 := rfl

#check mem_specialSet_iff
#check polyEvalP1_eq_polyMapPoints
#check polyMapPoints_some_mem_iff
#check derivative_eval_ne_zero_of_not_mem_specialSet
#check Mzk1Lemma22Target_to_fullShape
#check mzk1Lemma22TargetImpliesFullShape
#check fullShape_of_good
#check fullShape_of_induction
#check targetImpliesFullShapeRows_length
#print axioms Mzk1Lemma22Target_to_fullShape
#print axioms mzk1Lemma22TargetImpliesFullShape
#print axioms fullShape_of_induction

end LeanFormal.IUT.XiFPaper.Mzk1TargetImpliesFullShapeActual

end
