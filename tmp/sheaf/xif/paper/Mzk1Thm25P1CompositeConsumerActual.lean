import tmp.sheaf.xif.paper.Mzk1Lemma22RationalGateActual
import tmp.sheaf.xif.paper.Mzk1MoebiusP1Actual
import tmp.sheaf.xif.paper.Mzk1MoebiusP1CActual
import tmp.sheaf.xif.paper.Mzk1Thm25P1CompositeConsumerDesignActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

/-!
# Mzk1Thm25P1CompositeConsumerActual — REAL P1 composite consumer (F=Q scope)

STEP 0 prior-art (reuse, no re-proof):
* stage4 Mzk1Lemma22RationalGateActual (GREEN/CITABLE): mzk1Lemma22_target_rational :
  forall S beta, Lemma22Hypotheses S beta -> Mzk1Lemma22Target S beta (F=Q component);
* stepxi RestatedLemma22InterfaceActual: Mzk1Lemma22Target/Good/CV vocabulary (C-point);
* qpilot Mzk1MoebiusP1Actual (CITABLE 12): MoebiusData, mapPoints, specialSetQ, inversion,
  mapsTo_specialSetQ_iff, moebiusCriticalValues empty;
* qpilot Mzk1MoebiusP1CActual (CITABLE 14): C-typed MoebiusDataC, criticalValuesC transport;
* stepxi Mzk1Thm25P1CompositeConsumerDesignActual: P1CompositeRealConsumerTarget,
  CPointCriticalValuesIn01, MoebiusData (unique Q-typed source).

DELIVERED HERE (F=Q component of the REAL consumer):
1) P1CompositeRealConsumerTarget is PROVED from the rational 2.2 gate: for every
   paper-conditioned (S,beta) there is a nonconstant polynomial f carrying S into
   {0,1,infinity} inside P1(Q), carrying beta outside it, with C-point critical-value
   control (critical values over C in {0,1}).
2) 2.2 o 2.3 composition: composing the 2.2 polynomial map with the Moebius inversion
   (z |-> 1/z, which permutes {0,1,infinity} and has no critical points) yields a
   P1(Q) self-map preserving S into the special set and avoiding beta.
SCOPE (Lead A311/A313): rational inputs only; full P1(Qbar) reduction remains NAMED
(not complete).  NO closure claim; gate NOT PASSED; h22 binding HOLD.
Registry frozen 14041; no registry edits.  No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Thm25P1CompositeConsumerActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual
open LeanFormal.IUT.XiFPaper.RestatedLemma22InterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22RationalGateActual
open LeanFormal.IUT.XiFPaper.Mzk1Thm25P1CompositeConsumerDesignActual
open LeanFormal.IUT.XiFPaper.Mzk1MoebiusP1Actual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceScaleActual

/-- The restated vocabulary evaluation polyEvalP1 is the old polyMapPoints. -/
theorem polyEvalP1_eq_polyMapPoints (f : ℚ[X]) :
    polyEvalP1 f = polyMapPoints f := by
  funext p
  cases p <;> rfl

/-- Old specialSet = restated specialSet over Q. -/
theorem old_specialSet_eq_restated :
    Mzk1PolyMapActual.specialSet = (RestatedLemma24InterfaceActual.specialSet ℚ) := by
  ext p
  simp [Mzk1PolyMapActual.specialSet, RestatedLemma24InterfaceActual.specialSet]

/-- Old specialSet = qpilot specialSetQ. -/
theorem old_specialSet_eq_specialSetQ :
    Mzk1PolyMapActual.specialSet = Mzk1MoebiusP1Actual.specialSetQ := by
  ext p
  simp [Mzk1PolyMapActual.specialSet, Mzk1MoebiusP1Actual.specialSetQ]

/-- C-point critical-value control from the restated target's implication form. -/
theorem cpointCriticalValuesIn01_of_target {f : ℚ[X]}
    (hcrit : ∀ z : ℂ, Polynomial.aeval z f ∉ ({0, 1} : Set ℂ) →
      Polynomial.aeval z (Polynomial.derivative f) ≠ 0) :
    CPointCriticalValuesIn01 f := by
  intro z hz
  have hderiv : Polynomial.aeval z (Polynomial.derivative f) = 0 := by
    have h : (Polynomial.derivative (f.map (algebraMap ℚ ℂ))).eval z = 0 := hz
    rw [Polynomial.derivative_map, Polynomial.eval_map_algebraMap] at h
    exact h
  have hmem : Polynomial.aeval z f ∈ ({0, 1} : Set ℂ) := by
    by_contra hnot
    exact (hcrit z hnot) hderiv
  rcases hmem with h0 | h1
  · left
    rw [Polynomial.eval_map_algebraMap f z]
    exact h0
  · right
    rw [Polynomial.eval_map_algebraMap f z]
    exact h1

/-- The Moebius inversion z |-> 1/z is involutive on P1(Q). -/
theorem moebiusInversion_mapPoints_zero :
    moebiusInversion.mapPoints (P1Point.ofFinite (0 : ℚ)) = P1Point.infty := by
  simp [moebiusInversion, MoebiusData.mapPoints, P1Point.ofFinite, P1Point.infty]

theorem moebiusInversion_mapPoints_infty :
    moebiusInversion.mapPoints P1Point.infty = P1Point.ofFinite (0 : ℚ) := by
  simp [moebiusInversion, MoebiusData.mapPoints, P1Point.infty, P1Point.ofFinite]

theorem moebiusInversion_mapPoints_finite {x : ℚ} (hx : x ≠ 0) :
    moebiusInversion.mapPoints (P1Point.ofFinite x) = P1Point.ofFinite (1 / x) := by
  simp only [moebiusInversion, MoebiusData.mapPoints, P1Point.ofFinite]
  rw [if_neg (by simpa using hx)]
  congr 1
  field_simp [hx]
  ring

theorem moebiusInversion_involutive (p : P1Point ℚ) :
    moebiusInversion.mapPoints (moebiusInversion.mapPoints p) = p := by
  cases p with
  | none =>
      show moebiusInversion.mapPoints (moebiusInversion.mapPoints P1Point.infty) = P1Point.infty
      rw [moebiusInversion_mapPoints_infty, moebiusInversion_mapPoints_zero]
  | some x =>
      by_cases hx : x = 0
      · subst hx
        show moebiusInversion.mapPoints (moebiusInversion.mapPoints (P1Point.ofFinite (0 : ℚ))) =
          P1Point.ofFinite (0 : ℚ)
        rw [moebiusInversion_mapPoints_zero, moebiusInversion_mapPoints_infty]
      · have hx0 : x ≠ 0 := hx
        have hxinv : (1 : ℚ) / x ≠ 0 := by
          intro h
          field_simp at h
          norm_num at h
        show moebiusInversion.mapPoints (moebiusInversion.mapPoints (P1Point.ofFinite x)) =
          P1Point.ofFinite x
        rw [moebiusInversion_mapPoints_finite hx0, moebiusInversion_mapPoints_finite hxinv]
        congr 1
        field_simp

/-- **(1) F=Q REAL CONSUMER TARGET PROVED:** P1CompositeRealConsumerTarget holds for
rational inputs, from stage4's rational 2.2 gate. -/
theorem p1CompositeRealConsumerTarget_rational : P1CompositeRealConsumerTarget := by
  intro S β H
  obtain ⟨f, hdeg, hpres, hav, hcrit⟩ := mzk1Lemma22_target_rational S β H
  refine ⟨f, hdeg, ?_, ?_, ?_⟩
  · intro p hp
    have h1 := hpres p hp
    rw [polyEvalP1_eq_polyMapPoints, ← old_specialSet_eq_restated] at h1
    exact h1
  · have h1 := hav
    rw [polyEvalP1_eq_polyMapPoints, ← old_specialSet_eq_restated] at h1
    exact h1
  · exact cpointCriticalValuesIn01_of_target hcrit

/-- **(2) 2.2 o 2.3 COMPOSITION CONSUMER (F=Q):** composing the 2.2 polynomial map with
the Moebius inversion yields a P1(Q) self-map preserving S into {0,1,infinity} and
avoiding beta (the inversion permutes the special set and is involutive). -/
theorem p1Composite_mapPoints_consumer_rational :
    ∀ (S : Finset (P1Point ℚ)) (β : P1Point ℚ), Lemma22Hypotheses S β →
      ∃ g : P1Point ℚ → P1Point ℚ,
        (∀ p ∈ S, g p ∈ Mzk1PolyMapActual.specialSet) ∧
        g β ∉ Mzk1PolyMapActual.specialSet := by
  intro S β H
  obtain ⟨f, hdeg, hpres, hav, hcrit⟩ := mzk1Lemma22_target_rational S β H
  let M : MoebiusData := moebiusInversion
  let g : P1Point ℚ → P1Point ℚ := fun p => M.mapPoints (polyMapPoints f p)
  refine ⟨g, ?_, ?_⟩
  · intro p hp
    have h1 : polyMapPoints f p ∈ Mzk1MoebiusP1Actual.specialSetQ := by
      have h := hpres p hp
      rw [polyEvalP1_eq_polyMapPoints, ← old_specialSet_eq_restated] at h
      rwa [← old_specialSet_eq_specialSetQ]
    have h2 := Mzk1MoebiusP1Actual.moebiusInversion_mapsTo_specialSet h1
    simpa [g, M, old_specialSet_eq_specialSetQ] using h2
  · intro hmem
    have hmemQ : M.mapPoints (polyMapPoints f β) ∈ Mzk1MoebiusP1Actual.specialSetQ := by
      simpa [M, old_specialSet_eq_specialSetQ] using hmem
    have h2 := Mzk1MoebiusP1Actual.moebiusInversion_mapsTo_specialSet hmemQ
    have hinv : M.mapPoints (M.mapPoints (polyMapPoints f β)) = polyMapPoints f β :=
      moebiusInversion_involutive _
    rw [hinv] at h2
    have hnot : polyMapPoints f β ∉ Mzk1MoebiusP1Actual.specialSetQ := by
      intro h
      apply hav
      rw [polyEvalP1_eq_polyMapPoints, ← old_specialSet_eq_restated]
      rw [← old_specialSet_eq_specialSetQ] at h
      exact h
    exact hnot h2

/-- Consumer rows: (component, evidence, status/scope). -/
def p1CompositeConsumerRows : List (String × String × String) :=
  [ ("2.2 rational gate (F=Q)", "Mzk1Lemma22RationalGateActual.mzk1Lemma22_target_rational", "USED (stage4, CITABLE 5)"),
    ("restated 2.2 vocabulary", "Mzk1Lemma22Target / polyEvalP1 / specialSet / CPointCriticalValuesIn01", "USED (single source)"),
    ("(1) P1 composite real-consumer target", "p1CompositeRealConsumerTarget_rational", "PROVED (F=Q scope)"),
    ("C-point critical-value control", "cpointCriticalValuesIn01_of_target (aeval/eval casts)", "PROVED"),
    ("2.3 Moebius assets", "MoebiusData/mapPoints/specialSetQ/inversion/mapsTo_specialSetQ_iff (qpilot)", "USED (CITABLE 12)"),
    ("(2) 2.2 o 2.3 composition consumer", "p1Composite_mapPoints_consumer_rational (inversion involutive + special-set mapsTo)", "PROVED (F=Q scope)"),
    ("scope", "rational inputs only; full P1(Qbar) reduction NAMED (descent + fixed field + 2.3 over Qbar/C + AlgebraicNestedInductionInput)", "NO CLOSURE CLAIM; gate NOT PASSED"),
    ("h22 binding", "Mzk1Thm25UnconditionalActual (HOLD, off-queue)", "HISTORY ONLY") ]

theorem p1CompositeConsumerRows_length : p1CompositeConsumerRows.length = 8 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Thm25P1CompositeConsumerActual

end
