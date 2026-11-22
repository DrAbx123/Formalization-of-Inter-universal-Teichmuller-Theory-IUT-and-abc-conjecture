import tmp.sheaf.xif.paper.Mzk1P1MorphismInterfaceActual
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# Mzk1GChoiceScaleActual — lambda/scaling (g-choice) conjugation layer for [Mzk1] Lemma 2.2

STEP 0 prior-art (reuse, no re-proof): corpus [Mzk1] Lemma 2.1 ~35-105
(f(x)=x^m(x-1)^n, r=m/(m+n), f0=-min f), Lemma 2.2 lines 106-135 (apply Lemma 2.1
[C=2] to lambda*S with lambda positive rational); Mzk1P1MorphismInterfaceActual
(P1Point/P1Morphism); stage4 g-choice layers Mzk1Lemma21dAssemblyActual,
Mzk1PolyChainRuleActual, Mzk1PolyUnramifiedCompositionActual,
Mzk1Lemma22StatementShapeActual, Mzk1Lemma22StepConstructionActual.

Interface agreed with stage4 (13:0x).  DELIVERED HERE (PROVED): scaleP/scaleS,
Lemma22Hypotheses, ScaleOrdering data structure (supplied alpha1/alpha2 + order
hypotheses; the Finset-min extraction is separate bookkeeping), and the BASIC
memberships after lam := alpha2^{-1}: 0, 1, r=alpha1/alpha2 in scaled S with
0 < r < 1.  The residual target facts are recorded as Prop defs
(scale_memberships_statement with the ordering conjunct; ScaleRealHypotheses with the
Lemma-2.1 real-set package incl. m,n and r = m/(m+n)) for the next pass — they are NOT
claimed as proved here.

HONEST SCOPE: scaling bookkeeping + basic membership proofs only; no closure claim.
Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1GChoiceScaleActual

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual

/-- The paper hypotheses of [Mzk1] Lemma 2.2 (stage4-exact predicate). -/
def Lemma22Hypotheses (S : Finset (P1Point ℚ)) (β : P1Point ℚ) : Prop :=
  (P1Point.ofFinite (0 : ℚ) ∈ S) ∧
  (P1Point.infty ∈ S) ∧
  (∀ p ∈ S, p ≠ P1Point.ofFinite (0 : ℚ) → p ≠ P1Point.infty →
    ∃ x : ℚ, p = P1Point.ofFinite x ∧ 0 < x) ∧
  (β ∉ S) ∧
  (∀ p ∈ S, p ≠ P1Point.ofFinite (0 : ℚ) → p ≠ P1Point.infty →
    ∃ a b : ℚ, p = P1Point.ofFinite a ∧ β = P1Point.ofFinite b ∧ 2 ≤ b / a)

/-- (1) Rational scaling action on P^1: finite x maps to lam*x, infinity fixed. -/
def scaleP (lam : ℚ) : P1Point ℚ → P1Point ℚ
  | none => none
  | some x => some (lam * x)

/-- (2) The scaled finite set lam*S. -/
def scaleS (lam : ℚ) (S : Finset (P1Point ℚ)) : Finset (P1Point ℚ) :=
  S.image (scaleP lam)

@[simp] theorem scaleP_infty (lam : ℚ) :
    scaleP lam P1Point.infty = P1Point.infty := rfl

@[simp] theorem scaleP_ofFinite (lam x : ℚ) :
    scaleP lam (P1Point.ofFinite x) = P1Point.ofFinite (lam * x) := rfl

/-- The scaled image of a finite point of S lies in the scaled set. -/
theorem mem_scaleS_of_mem {lam x : ℚ} {S : Finset (P1Point ℚ)}
    (hx : P1Point.ofFinite x ∈ S) :
    P1Point.ofFinite (lam * x) ∈ scaleS lam S := by
  unfold scaleS
  exact Finset.mem_image_of_mem (scaleP lam) hx

/-- 0 stays in the scaled set. -/
theorem zero_mem_scaleS {lam : ℚ} {S : Finset (P1Point ℚ)}
    (h : P1Point.ofFinite (0 : ℚ) ∈ S) :
    P1Point.ofFinite (0 : ℚ) ∈ scaleS lam S := by
  simpa using mem_scaleS_of_mem (lam := lam) (x := (0 : ℚ)) h

/-- lam*alpha = 1 for lam = alpha^{-1}, alpha > 0. -/
theorem inv_mul_alpha2 {alpha : ℚ} (h : 0 < alpha) : alpha⁻¹ * alpha = 1 :=
  inv_mul_cancel₀ (ne_of_gt h)

/-- (3) **Ordering data:** two positive finite points alpha1 < alpha2 of S with the
paper ordering hypotheses (stage4 supplies them; Finset-min extraction is separate
bookkeeping, recorded as remaining). -/
structure ScaleOrdering (S : Finset (P1Point ℚ)) where
  alpha1 : ℚ
  alpha2 : ℚ
  mem0 : P1Point.ofFinite (0 : ℚ) ∈ S
  memInf : P1Point.infty ∈ S
  mem1 : P1Point.ofFinite alpha1 ∈ S
  mem2 : P1Point.ofFinite alpha2 ∈ S
  pos1 : 0 < alpha1
  lt : alpha1 < alpha2
  partition : ∀ p ∈ S, p ≠ P1Point.ofFinite (0 : ℚ) → p ≠ P1Point.infty →
    p = P1Point.ofFinite alpha1 ∨ p = P1Point.ofFinite alpha2 ∨
      (∃ x : ℚ, p = P1Point.ofFinite x ∧ alpha2 < x)
  le_first : ∀ a : ℚ, P1Point.ofFinite a ∈ S → 0 < a → alpha1 ≤ a
  le_second : ∀ a : ℚ, P1Point.ofFinite a ∈ S → 0 < a → alpha1 < a → alpha2 ≤ a

/-- (4a) **Basic memberships after lam := alpha2^{-1} (PROVED):** scaled S contains
0, 1 and r = alpha1/alpha2, with 0 < r < 1. -/
theorem scale_memberships_basic (S : Finset (P1Point ℚ)) (O : ScaleOrdering S) :
    let lam : ℚ := O.alpha2⁻¹
    P1Point.ofFinite (0 : ℚ) ∈ scaleS lam S ∧
    P1Point.ofFinite (1 : ℚ) ∈ scaleS lam S ∧
    P1Point.ofFinite (O.alpha1 / O.alpha2) ∈ scaleS lam S ∧
    0 < O.alpha1 / O.alpha2 ∧ O.alpha1 / O.alpha2 < 1 := by
  have hα2pos : 0 < O.alpha2 := lt_trans O.pos1 O.lt
  refine ⟨zero_mem_scaleS O.mem0, ?_, ?_, div_pos O.pos1 hα2pos, ?_⟩
  · have h := mem_scaleS_of_mem (lam := O.alpha2⁻¹) (x := O.alpha2) O.mem2
    simpa [inv_mul_alpha2 hα2pos] using h
  · have h := mem_scaleS_of_mem (lam := O.alpha2⁻¹) (x := O.alpha1) O.mem1
    simpa [div_eq_inv_mul] using h
  · rw [div_lt_one hα2pos]
    exact O.lt

/-- (4b) Residual target statement (NOT proved here): the full membership/ordering
conjunct of the agreed interface. -/
def scale_memberships_statement (S : Finset (P1Point ℚ)) (O : ScaleOrdering S) : Prop :=
  let lam : ℚ := O.alpha2⁻¹
  (∀ p ∈ scaleS lam S, p ≠ P1Point.ofFinite (0 : ℚ) →
    p ≠ P1Point.ofFinite (1 : ℚ) →
    p ≠ P1Point.ofFinite (O.alpha1 / O.alpha2) →
    p ≠ P1Point.infty →
    ∃ x : ℚ, p = P1Point.ofFinite x ∧ 1 < x)

/-- (4c) **Full ordering conjunct (PROVED):** for lam := alpha2^{-1}, every finite
scaled point other than 0, 1, r = alpha1/alpha2 is > 1 (the ordering data of
ScaleOrdering supplies the partition of S). -/
theorem scale_memberships_full (S : Finset (P1Point ℚ)) (O : ScaleOrdering S) :
    scale_memberships_statement S O := by
  intro p hp h0 h1 hr hinf
  have hα2pos : 0 < O.alpha2 := lt_trans O.pos1 O.lt
  have hα2ne : O.alpha2 ≠ 0 := ne_of_gt hα2pos
  have hmem : p ∈ scaleS O.alpha2⁻¹ S := hp
  unfold scaleS at hmem
  obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hmem
  have hqS : q ∈ S := hq
  have hq0 : q ≠ P1Point.ofFinite (0 : ℚ) := by
    intro h
    apply h0
    rw [← hqp, h]
    simp [scaleP, P1Point.ofFinite]
  have hqinf : q ≠ P1Point.infty := by
    intro h
    apply hinf
    rw [← hqp, h]
    rfl
  rcases O.partition q hqS hq0 hqinf with hA | hB | ⟨x, hxq, hxgt⟩
  · -- q = alpha1: image is r, contradicting hr
    exfalso
    apply hr
    rw [← hqp, hA]
    change P1Point.ofFinite (O.alpha2⁻¹ * O.alpha1) = P1Point.ofFinite (O.alpha1 / O.alpha2)
    rw [div_eq_inv_mul]
  · -- q = alpha2: image is 1, contradicting h1
    exfalso
    apply h1
    rw [← hqp, hB]
    change P1Point.ofFinite (O.alpha2⁻¹ * O.alpha2) = P1Point.ofFinite (1 : ℚ)
    rw [inv_mul_alpha2 hα2pos]
  · -- q = x > alpha2: image lam*x = x/alpha2 > 1
    refine ⟨O.alpha2⁻¹ * x, ?_, ?_⟩
    · rw [← hqp, hxq]
      rfl
    · have : O.alpha2⁻¹ * x = x / O.alpha2 := by rw [div_eq_inv_mul]
      rw [this]
      rw [one_lt_div hα2pos]
      exact hxgt

/-- (5) Residual target package (NOT proved here): the real finite set for Lemma 2.1
with 0,1,r in it, m,n >= 1, r = m/(m+n), ordering, and the separated-beta condition.
scaledRealS is the finite part of the scaled set cast to reals. -/
def ScaleRealHypotheses (S : Finset (P1Point ℚ)) (b : ℚ) (O : ScaleOrdering S)
    (scaledRealS : Finset ℝ) : Prop :=
  let lam : ℚ := O.alpha2⁻¹
  let r : ℚ := O.alpha1 / O.alpha2
  (∃ scaledRatS : Finset ℚ, scaledRealS = scaledRatS.image (fun q : ℚ => (q : ℝ))) ∧
  scaledRealS.Nonempty ∧ (0 : ℝ) ∈ scaledRealS ∧ (1 : ℝ) ∈ scaledRealS ∧
  ((r : ℚ) : ℝ) ∈ scaledRealS ∧ 0 < ((r : ℚ) : ℝ) ∧ ((r : ℚ) : ℝ) < 1 ∧
  (∃ m n : ℕ, 1 ≤ m ∧ 1 ≤ n ∧ ((r : ℚ) : ℝ) = (m : ℝ) / ((m + n : ℕ) : ℝ)) ∧
  (∀ x ∈ scaledRealS, x ≠ 0 → x ≠ 1 → x ≠ ((r : ℚ) : ℝ) → 1 < x) ∧
  (∀ x ∈ scaledRealS, x ≠ 0 → 2 ≤ (((lam * b : ℚ) : ℝ) / x))

/-- Rows: (scaling component, Lean evidence, status). -/
def gChoiceScaleRows : List (String × String × String) :=
  [ ("scaleP / scaleS (P^1 and finite set scaling)", "scaleP / scaleS (defs)", "DEFINED"),
    ("Lemma 2.2 paper-conditioned hypotheses predicate", "Lemma22Hypotheses", "DEFINED"),
    ("ordering data (two smallest positive finite points + order hypotheses)", "ScaleOrdering (structure; supplied by stage4; Finset-min extraction pending)", "DATA INTERFACE"),
    ("0, 1, r = alpha1/alpha2 membership + 0<r<1 after lam = alpha2^{-1}", "scale_memberships_basic", "PROVED"),
    ("full ordering conjunct of the agreed interface", "scale_memberships_full (PROVED; proves scale_memberships_statement)", "PROVED"),
    ("Lemma 2.1 real-set package (0,1,r, m,n, r=m/(m+n), ordering, separation)", "ScaleRealHypotheses (Prop target package, not proved)", "PENDING (next pass)"),
    ("g-choice polynomial / chain rule / full Lemma 2.2", "stage4 layers (not re-proved here)", "stage4 scope; no closure claim") ]

theorem gChoiceScaleRows_length : gChoiceScaleRows.length = 7 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1GChoiceScaleActual

end
