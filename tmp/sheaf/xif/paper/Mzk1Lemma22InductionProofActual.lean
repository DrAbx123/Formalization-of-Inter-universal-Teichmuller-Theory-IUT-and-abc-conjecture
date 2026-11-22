import tmp.sheaf.xif.paper.RestatedLemma22InterfaceActual
import tmp.sheaf.xif.paper.Mzk1Lemma22StepInterfaceQActual
import tmp.sheaf.xif.paper.Mzk1Lemma22StepInterfaceQProofActual
import tmp.sheaf.xif.paper.Mzk1Lemma22CritValueActual
import tmp.sheaf.xif.paper.Mzk1PolyMapActual
import Mathlib.Tactic

/-! # Mzk1Lemma22InductionProofActual — CONDITIONAL flat Good induction (F=Q component)

STEP 0 prior-art / SCOPE (Lead A311-A319; recompile marker 2026-11-10T21:26): rational (P1Point Q) component of paper Lemma 2.2
(base case m(S)=0); algebraic (P1Point Qbar, m/d nested induction) scope is out of this gate.
This file is CONDITIONAL on two explicitly named inputs (BaseProviderStatement and
StepProviderStatement, the latter carrying the C-point CV-in-image property of the step
polynomial).  It does NOT claim paper closure; gate NOT PASSED; binding HOLD.

INTEGRITY NOTE (Lead A356; 谢德 re-audit): the proven chain uses the UNCHANGED stepxi
Good (C-point condition: aeval z f ∉ {0,1} -> aeval z f.derivative ≠ 0).  The unnormalized gPoly
does NOT satisfy the literal 0/1 critical-value statement (refuted in Mzk1CritValueInImageProofActual);
intermediate steps use the IMAGE-BASED CritValueInImageStatement, and the composite's C-point
condition is derived via the two chain-rule cases.  Base f = C c * X satisfies it vacuously
(derivative = C c ≠ 0).  Mzk1BaseProviderProofActual (sorryAx) is NOT used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma22InductionProofActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceScaleActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual
open LeanFormal.IUT.XiFPaper.RestatedLemma22InterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22StepInterfaceQActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22CritValueActual

/-- bridge: polyMapPoints (used by the step interface) and polyEvalP1 (used by Good)
are the same map. -/
theorem polyMapPoints_eq_polyEvalP1 (f : ℚ[X]) (p : P1Point ℚ) :
    polyMapPoints f p = polyEvalP1 f p := by
  cases p with
  | none => rfl
  | some x => rfl

/-- bridge: polyEvalP1 of a composite is the composition of polyEvalP1. -/
theorem polyEvalP1_comp (h g : ℚ[X]) (p : P1Point ℚ) :
    polyEvalP1 (h.comp g) p = polyEvalP1 h (polyEvalP1 g p) := by
  cases p with
  | none => rfl
  | some x => simp [polyEvalP1, Polynomial.eval_comp]

/-- NAMED input (base provider): Good polynomial for |S| <= 3 under Lemma22Hypotheses. -/
def BaseProviderStatement : Prop :=
  ∀ (S : Finset (P1Point ℚ)) (β : P1Point ℚ), S.card ≤ 3 →
    Lemma22Hypotheses S β → ∃ f : ℚ[X], Good f S β

/-- NAMED input (step provider): explicit gPoly step for 3 < |S|, carrying the IMAGE-BASED
C-point critical-value-in-image property of the step polynomial (paper Lemma 2.2(i): every
critical value over C is gPoly(p) for some p in the source S).  NOTE: the literal 0/1
critical-value condition is FALSE for the unnormalized gPoly (kernel-checked counterexample
in Mzk1CritValueInImageProofActual); 0/1 holds only for the Belyi-normalized polynomial. -/
def StepProviderStatement : Prop :=
  ∀ (S : Finset (P1Point ℚ)) (β : P1Point ℚ), 3 < S.card →
    Lemma22Hypotheses S β →
      ∃ st : Mzk1Lemma22StepInterfaceQ,
        st.source = S ∧ st.beta = β ∧ st.targetS.card < S.card ∧
        (∀ z : ℂ, Polynomial.aeval z (Polynomial.derivative st.g) = 0 →
          ∃ p ∈ st.source, ∃ v : ℚ, (v : ℂ) = Polynomial.aeval z st.g ∧
            polyEvalP1 st.g p = P1Point.ofFinite v)

/-- CONDITIONAL induction: named base/step inputs imply the restated induction statement. -/
theorem mzk1Lemma22_induction_conditional
    (hbase : BaseProviderStatement) (hstep : StepProviderStatement) :
    Mzk1Lemma22InductionStatement := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S β hcard H
    by_cases h3 : S.card ≤ 3
    · exact hbase S β h3 H
    · have hbig : 3 < S.card := by omega
      obtain ⟨st, hsrc, hbeta, hcardlt, hcv⟩ := hstep S β hbig H
      have hnlt : st.targetS.card < n := by omega
      obtain ⟨h, hGood⟩ := ih st.targetS.card hnlt st.targetS st.beta' le_rfl st.hImage
      refine ⟨h.comp st.g, ?_, ?_, ?_, ?_⟩
      · -- degree
        rw [Polynomial.natDegree_comp]
        exact Nat.mul_pos hGood.1 st.gdeg
      · -- preserves
        intro p hp
        have hpS : p ∈ st.source := by rwa [hsrc]
        have hgp : polyEvalP1 st.g p ∈ st.targetS := by
          rw [← polyMapPoints_eq_polyEvalP1]
          exact st.preserves p hpS
        have hh := hGood.2.1 (polyEvalP1 st.g p) hgp
        rw [polyEvalP1_comp]
        exact hh
      · -- avoids
        obtain ⟨_, _, _, hβnotinT, _⟩ := st.hImage
        have hβ' : st.beta' = polyEvalP1 st.g β := by
          rw [st.beta'_eq, hbeta, polyMapPoints_eq_polyEvalP1]
        have hgβ : polyEvalP1 st.g β ∉ st.targetS := by
          rw [← hβ']
          exact hβnotinT
        have hh := hGood.2.2.1
        rw [polyEvalP1_comp, ← hβ']
        exact hh
      · -- C-point unramified via the step's CV-in-image property
        intro z hzne hzder
        have hchain0 : Polynomial.aeval z (Polynomial.derivative (h.comp st.g)) = 0 := hzder
        rw [Polynomial.derivative_comp, Polynomial.aeval_mul, Polynomial.aeval_comp] at hchain0
        have hvalcomp : Polynomial.aeval z (h.comp st.g) =
            Polynomial.aeval (Polynomial.aeval z st.g) h := by
          rw [Polynomial.aeval_comp]
        rcases mul_eq_zero.mp hchain0 with hg' | hh'
        · obtain ⟨p, hpS, v, hv, hgpv⟩ := hcv z hg'
          have hgpv' : polyMapPoints st.g p = P1Point.ofFinite v := by
            rw [polyMapPoints_eq_polyEvalP1]
            exact hgpv
          have hmemT : P1Point.ofFinite v ∈ st.targetS := by
            rw [st.targetS_eq]
            exact Finset.mem_image.mpr ⟨p, hpS, hgpv'⟩
          have hh := hGood.2.1 (P1Point.ofFinite v) hmemT
          have hval01 : Polynomial.aeval (v : ℂ) h = 0 ∨ Polynomial.aeval (v : ℂ) h = 1 := by
            have hh' : P1Point.ofFinite (Polynomial.eval v h) ∈
                RestatedLemma24InterfaceActual.specialSet ℚ := by
              simpa [polyEvalP1, P1Point.ofFinite] using hh
            simp only [RestatedLemma24InterfaceActual.specialSet, Set.mem_insert_iff,
              Set.mem_singleton_iff, P1Point.ofFinite, P1Point.infty,
              Option.some.injEq] at hh'
            rcases hh' with h' | h' | h'
            · exact absurd h' (by simp)
            · left
              rw [aeval_cast_eval, h']
              norm_num
            · right
              rw [aeval_cast_eval, h']
              norm_num
          have hfinal : Polynomial.aeval z (h.comp st.g) = 0 ∨
              Polynomial.aeval z (h.comp st.g) = 1 := by
            rw [hvalcomp, ← hv]
            exact hval01
          exact hzne hfinal
        · have hnot : Polynomial.aeval (Polynomial.aeval z st.g) h ∉ ({0, 1} : Set ℂ) := by
            rw [← hvalcomp]
            exact hzne
          have hhne : Polynomial.aeval (Polynomial.aeval z st.g)
              (Polynomial.derivative h) ≠ 0 :=
            hGood.2.2.2 (Polynomial.aeval z st.g) hnot
          exact hhne hh'

/-- Corollary: conditional restated target from the two named inputs. -/
theorem mzk1Lemma22_target_conditional
    (hbase : BaseProviderStatement) (hstep : StepProviderStatement)
    (S : Finset (P1Point ℚ)) (β : P1Point ℚ) (H : Lemma22Hypotheses S β) :
    Mzk1Lemma22Target S β :=
  target_of_induction (mzk1Lemma22_induction_conditional hbase hstep) S β H

def inductionProofRows : List (String × String × String) :=
  [ ("base provider |S|<=3 Good", "NAMED INPUT", "BaseProviderStatement (BaseGood WIP)")
  , ("step provider + C-point CV-in-image", "NAMED INPUT", "StepProviderStatement (green g-choice chain + CritValueInImageStatement)")
  , ("conditional induction statement", "PROVED CONDITIONAL", "mzk1Lemma22_induction_conditional")
  , ("conditional restated target", "PROVED CONDITIONAL", "mzk1Lemma22_target_conditional")
  , ("scope", "F=Q COMPONENT", "Qbar/m-d nested induction out of this gate (named reduction layer)")
  , ("closure", "NOT CLAIMED", "gate NOT PASSED; binding HOLD") ]

theorem inductionProofRows_length : inductionProofRows.length = 6 := rfl

#check mzk1Lemma22_induction_conditional
#check mzk1Lemma22_target_conditional

end LeanFormal.IUT.XiFPaper.Mzk1Lemma22InductionProofActual
end
