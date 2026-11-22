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

/-- The finite rational part of the scaled set (infinity dropped). -/
def scaleRatS (lam : ℚ) (S : Finset (P1Point ℚ)) : Finset ℚ :=
  ((scaleS lam S).erase P1Point.infty).image
    (fun p => match p with
      | none => 0
      | some x => x)

/-- The real finite set of the scaled set (for Lemma 2.1). -/
def scaleRealS (lam : ℚ) (S : Finset (P1Point ℚ)) : Finset ℝ :=
  (scaleRatS lam S).image (fun q : ℚ => (q : ℝ))

/-- Coercion equation for stage4's f0q coercion: scaleRealS is the cast of scaleRatS. -/
theorem scaleRealS_eq_image (lam : ℚ) (S : Finset (P1Point ℚ)) :
    scaleRealS lam S = (scaleRatS lam S).image (fun q : ℚ => (q : ℝ)) := rfl

theorem ofFinite_ne_infty' (q : ℚ) :
    P1Point.ofFinite q ≠ P1Point.infty := by
  simp [P1Point.infty, P1Point.ofFinite]

theorem mem_scaleRatS_of_mem_scaleS {lam q : ℚ} {S : Finset (P1Point ℚ)}
    (h : P1Point.ofFinite q ∈ scaleS lam S) : q ∈ scaleRatS lam S := by
  unfold scaleRatS
  refine Finset.mem_image.mpr ⟨P1Point.ofFinite q, ?_, rfl⟩
  exact Finset.mem_erase.mpr ⟨ofFinite_ne_infty' q, h⟩

theorem mem_scaleRealS_of_mem_scaleRatS {lam : ℚ} {q : ℚ} {S : Finset (P1Point ℚ)}
    (h : q ∈ scaleRatS lam S) : (q : ℝ) ∈ scaleRealS lam S :=
  Finset.mem_image_of_mem (fun q : ℚ => (q : ℝ)) h

/-- Extract the rational representative of a member of scaleRatS as a finite point of
the scaled set. -/
theorem mem_scaleS_of_mem_scaleRatS {lam : ℚ} {q : ℚ} {S : Finset (P1Point ℚ)}
    (h0S : P1Point.ofFinite (0 : ℚ) ∈ scaleS lam S) (h : q ∈ scaleRatS lam S) :
    P1Point.ofFinite q ∈ scaleS lam S := by
  unfold scaleRatS at h
  obtain ⟨p, hp, hpq⟩ := Finset.mem_image.mp h
  rw [Finset.mem_erase] at hp
  rcases p with _ | q'
  · have hq0 : q = 0 := by simpa using hpq.symm
    rw [hq0]
    exact h0S
  · have hqq' : q' = q := hpq
    rw [← hqq']
    exact hp.2

/-- **(6) The real-set package (PROVED):** for lam := alpha2^{-1} and
r := alpha1/alpha2, the real finite part of the scaled set satisfies
ScaleRealHypotheses for any m,n >= 1 representing r = m/(m+n), given the paper
separation row (m,n are supplied by stage4's g-choice). -/
theorem scale_realHypotheses_exists (S : Finset (P1Point ℚ)) (b : ℚ) (O : ScaleOrdering S)
    (hpos : ∀ p ∈ S, p ≠ P1Point.ofFinite (0 : ℚ) → p ≠ P1Point.infty →
      ∃ x : ℚ, p = P1Point.ofFinite x ∧ 0 < x)
    (hsep : ∀ a : ℚ, P1Point.ofFinite a ∈ S → 0 < a → 2 ≤ b / a)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hr : ((O.alpha1 / O.alpha2 : ℚ) : ℝ) = (m : ℝ) / ((m + n : ℕ) : ℝ)) :
    ScaleRealHypotheses S b O (scaleRealS O.alpha2⁻¹ S) := by
  have hα2pos : 0 < O.alpha2 := lt_trans O.pos1 O.lt
  have hlampos : 0 < O.alpha2⁻¹ := inv_pos.mpr hα2pos
  have hlamne : O.alpha2⁻¹ ≠ 0 := ne_of_gt hlampos
  obtain ⟨h0mem, h1mem, hrmem, hrpos, hrlt⟩ := scale_memberships_basic S O
  have hfull := scale_memberships_full S O
  have h0rat : (0 : ℚ) ∈ scaleRatS O.alpha2⁻¹ S :=
    mem_scaleRatS_of_mem_scaleS h0mem
  have h1rat : (1 : ℚ) ∈ scaleRatS O.alpha2⁻¹ S :=
    mem_scaleRatS_of_mem_scaleS (by simpa using h1mem)
  have hrrat : O.alpha1 / O.alpha2 ∈ scaleRatS O.alpha2⁻¹ S :=
    mem_scaleRatS_of_mem_scaleS hrmem
  have h0real : (0 : ℝ) ∈ scaleRealS O.alpha2⁻¹ S := by
    simpa using mem_scaleRealS_of_mem_scaleRatS h0rat
  have h1real : (1 : ℝ) ∈ scaleRealS O.alpha2⁻¹ S := by
    simpa using mem_scaleRealS_of_mem_scaleRatS h1rat
  have hrreal : ((O.alpha1 / O.alpha2 : ℚ) : ℝ) ∈ scaleRealS O.alpha2⁻¹ S :=
    mem_scaleRealS_of_mem_scaleRatS hrrat
  refine ⟨⟨scaleRatS O.alpha2⁻¹ S, rfl⟩, ⟨(0 : ℝ), h0real⟩, h0real, h1real, hrreal,
    ?_, ?_, ⟨m, n, hm, hn, hr⟩, ?_, ?_⟩
  · exact_mod_cast hrpos
  · exact_mod_cast hrlt
  · -- ordering: every real point other than 0, 1, r is > 1
    intro x hx hx0 hx1 hxr
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    have hqS : P1Point.ofFinite q ∈ scaleS O.alpha2⁻¹ S :=
      mem_scaleS_of_mem_scaleRatS (zero_mem_scaleS O.mem0) hq
    have hq0 : P1Point.ofFinite q ≠ P1Point.ofFinite (0 : ℚ) := by
      intro h
      apply hx0
      have hqeq : q = 0 := by simpa [P1Point.ofFinite] using h
      rw [hqeq]
      norm_num
    have hq1 : P1Point.ofFinite q ≠ P1Point.ofFinite (1 : ℚ) := by
      intro h
      apply hx1
      have hqeq : q = 1 := by simpa [P1Point.ofFinite] using h
      rw [hqeq]
      norm_num
    have hqr : P1Point.ofFinite q ≠ P1Point.ofFinite (O.alpha1 / O.alpha2) := by
      intro h
      apply hxr
      have hqeq : q = O.alpha1 / O.alpha2 := by simpa [P1Point.ofFinite] using h
      rw [hqeq]
    have hqinf : P1Point.ofFinite q ≠ P1Point.infty := ofFinite_ne_infty' q
    obtain ⟨y, hyq, hygt⟩ := hfull (P1Point.ofFinite q) hqS hq0 hq1 hqr hqinf
    have hy : q = y := by simpa [P1Point.ofFinite] using hyq
    subst hy
    exact_mod_cast hygt
  · -- separation: (lam*b)/x >= 2 for every nonzero real point x
    intro x hx hx0
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    have hqS : P1Point.ofFinite q ∈ scaleS O.alpha2⁻¹ S :=
      mem_scaleS_of_mem_scaleRatS (zero_mem_scaleS O.mem0) hq
    unfold scaleS at hqS
    obtain ⟨r0, hr0, hpr⟩ := Finset.mem_image.mp hqS
    rcases r0 with _ | a
    · simp [scaleP, P1Point.ofFinite] at hpr
    · simp [scaleP, P1Point.ofFinite] at hpr
      have hqeq : q = O.alpha2⁻¹ * a := hpr.symm
      have hane0 : a ≠ 0 := by
        intro ha
        apply hx0
        rw [hqeq, ha, mul_zero]
        norm_num
      have hapos : 0 < a := by
        obtain ⟨y, hya, hypos⟩ := hpos (P1Point.ofFinite a) hr0
          (by intro h; exact hane0 (by simpa [P1Point.ofFinite] using h))
          (ofFinite_ne_infty' a)
        have hay : a = y := by simpa [P1Point.ofFinite] using hya
        rwa [hay]
      rw [hqeq]
      have hdiv : ((O.alpha2⁻¹ * b : ℚ) : ℝ) / ((O.alpha2⁻¹ * a : ℚ) : ℝ) =
          (b / a : ℚ) := by
        push_cast
        field_simp [ne_of_gt hlampos, ne_of_gt hapos]
      rw [hdiv]
      exact_mod_cast hsep a hr0 hapos

/-- The finite set of positive rational points of S (0 and infinity excluded);
used for the two-smallest-point extraction. -/
def posRatS (S : Finset (P1Point ℚ)) : Finset ℚ :=
  ((S.erase (P1Point.ofFinite (0 : ℚ))).erase P1Point.infty).image
    (fun p => match p with
      | none => 0
      | some x => x)

theorem mem_posRatS_of_mem {S : Finset (P1Point ℚ)} {x : ℚ} {p : P1Point ℚ}
    (hpS : p ∈ S) (h0 : p ≠ P1Point.ofFinite (0 : ℚ)) (hinf : p ≠ P1Point.infty)
    (hpx : p = P1Point.ofFinite x) : x ∈ posRatS S := by
  unfold posRatS
  refine Finset.mem_image.mpr ⟨p, ?_, ?_⟩
  · rw [Finset.mem_erase, Finset.mem_erase]
    exact ⟨hinf, h0, hpS⟩
  · rw [hpx]
    rfl

theorem exists_of_mem_posRatS {S : Finset (P1Point ℚ)} {x : ℚ} (h : x ∈ posRatS S) :
    ∃ p, p ∈ S ∧ p ≠ P1Point.ofFinite (0 : ℚ) ∧ p ≠ P1Point.infty ∧
      p = P1Point.ofFinite x := by
  unfold posRatS at h
  obtain ⟨p, hp, hpx⟩ := Finset.mem_image.mp h
  rw [Finset.mem_erase, Finset.mem_erase] at hp
  obtain ⟨hpinf, hp0, hpS⟩ := hp
  rcases p with _ | y
  · exact absurd rfl hpinf
  · simp only [Option.some.injEq] at hpx
    exact ⟨P1Point.ofFinite y, hpS, hp0, hpinf, by rw [hpx]⟩

theorem posRatS_card (S : Finset (P1Point ℚ))
    (h0 : P1Point.ofFinite (0 : ℚ) ∈ S) (hinf : P1Point.infty ∈ S) :
    (posRatS S).card = S.card - 2 := by
  unfold posRatS
  have hmem : P1Point.infty ∈ S.erase (P1Point.ofFinite (0 : ℚ)) := by
    rw [Finset.mem_erase]
    exact ⟨(ofFinite_ne_infty' 0).symm, hinf⟩
  have e1 : (S.erase (P1Point.ofFinite (0 : ℚ))).card = S.card - 1 :=
    Finset.card_erase_of_mem h0
  have e2 : ((S.erase (P1Point.ofFinite (0 : ℚ))).erase P1Point.infty).card =
      (S.erase (P1Point.ofFinite (0 : ℚ))).card - 1 :=
    Finset.card_erase_of_mem hmem
  have hinj : Set.InjOn (fun p : P1Point ℚ => match p with
      | none => 0
      | some x => x)
      (↑((S.erase (P1Point.ofFinite (0 : ℚ))).erase P1Point.infty) :
        Set (P1Point ℚ)) := by
    intro p hp q hq hpq
    rw [Finset.mem_coe, Finset.mem_erase, Finset.mem_erase] at hp hq
    obtain ⟨hpinf, -, -⟩ := hp
    obtain ⟨hqinf, -, -⟩ := hq
    rcases p with _ | x
    · exact absurd rfl hpinf
    · rcases q with _ | y
      · exact absurd rfl hqinf
      · simpa [Option.some.injEq] using hpq
  rw [Finset.card_image_iff.mpr hinj, e2, e1]
  omega

/-- **Finset-min extraction of the two smallest positive finite points:** from the
Lemma 2.2 paper hypotheses and 3 < |S|, the two smallest elements of posRatS give a
ScaleOrdering (removes stage4's fallback for the ordering data). -/
noncomputable def scaleOrdering (S : Finset (P1Point ℚ))
    (h0 : P1Point.ofFinite (0 : ℚ) ∈ S) (hinf : P1Point.infty ∈ S)
    (hpos : ∀ p ∈ S, p ≠ P1Point.ofFinite (0 : ℚ) → p ≠ P1Point.infty →
      ∃ x : ℚ, p = P1Point.ofFinite x ∧ 0 < x)
    (hcard : 3 < S.card) : ScaleOrdering S := by
  classical
  let T := posRatS S
  have hTcard : 2 ≤ T.card := by
    have hc := posRatS_card S h0 hinf
    unfold T
    rw [hc]
    omega
  have hneT : T.Nonempty := Finset.card_pos.mp (by omega)
  let a1 := T.min' hneT
  have ha1 : a1 ∈ T := Finset.min'_mem T hneT
  have hneT2 : (T.erase a1).Nonempty := by
    apply Finset.card_pos.mp
    have hc : (T.erase a1).card = T.card - 1 := Finset.card_erase_of_mem ha1
    omega
  let a2 := (T.erase a1).min' hneT2
  have ha2erase : a2 ∈ T.erase a1 := Finset.min'_mem _ hneT2
  have ha2 : a2 ∈ T := (Finset.mem_erase.mp ha2erase).2
  have ha2ne : a2 ≠ a1 := (Finset.mem_erase.mp ha2erase).1
  have hle12 : a1 ≤ a2 := Finset.min'_le T a2 ha2
  have hlt12 : a1 < a2 := lt_of_le_of_ne hle12 (Ne.symm ha2ne)
  let p1 := Classical.choose (exists_of_mem_posRatS ha1)
  have hp1spec := Classical.choose_spec (exists_of_mem_posRatS ha1)
  have hp1S : p1 ∈ S := hp1spec.1
  have hp1_0 : p1 ≠ P1Point.ofFinite (0 : ℚ) := hp1spec.2.1
  have hp1_inf : p1 ≠ P1Point.infty := hp1spec.2.2.1
  have hp1eq : p1 = P1Point.ofFinite a1 := hp1spec.2.2.2
  let p2 := Classical.choose (exists_of_mem_posRatS ha2)
  have hp2spec := Classical.choose_spec (exists_of_mem_posRatS ha2)
  have hp2S : p2 ∈ S := hp2spec.1
  have hp2_0 : p2 ≠ P1Point.ofFinite (0 : ℚ) := hp2spec.2.1
  have hp2_inf : p2 ≠ P1Point.infty := hp2spec.2.2.1
  have hp2eq : p2 = P1Point.ofFinite a2 := hp2spec.2.2.2
  have hpos1 : 0 < a1 := by
    obtain ⟨y, hpy, hypos⟩ := hpos p1 hp1S hp1_0 hp1_inf
    have hy : y = a1 := by
      have h : P1Point.ofFinite y = P1Point.ofFinite a1 := by rw [← hpy, hp1eq]
      simpa [P1Point.ofFinite] using h
    rwa [hy] at hypos
  refine ⟨a1, a2, h0, hinf, ?_, ?_, hpos1, hlt12, ?_, ?_, ?_⟩
  · rwa [← hp1eq]
  · rwa [← hp2eq]
  · intro p hpS hp0 hinf'
    obtain ⟨x, hpx, hxpos⟩ := hpos p hpS hp0 hinf'
    have hxT : x ∈ T := mem_posRatS_of_mem hpS hp0 hinf' hpx
    by_cases hx1 : x = a1
    · exact Or.inl (by rw [hpx, hx1])
    · have hxerase : x ∈ T.erase a1 := Finset.mem_erase.mpr ⟨hx1, hxT⟩
      have hle : a2 ≤ x := Finset.min'_le _ x hxerase
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact Or.inr (Or.inr ⟨x, hpx, hlt⟩)
      · exact Or.inr (Or.inl (by rw [hpx, ← heq]))
  · intro a ha hapos
    have haT : a ∈ T :=
      mem_posRatS_of_mem ha
        (by
          intro h
          have ha0 : a = 0 := by simpa [P1Point.ofFinite] using h
          rw [ha0] at hapos
          exact lt_irrefl _ hapos)
        (ofFinite_ne_infty' a) rfl
    exact Finset.min'_le T a haT
  · intro a ha hapos ha1
    have haT : a ∈ T :=
      mem_posRatS_of_mem ha
        (by
          intro h
          have ha0 : a = 0 := by simpa [P1Point.ofFinite] using h
          rw [ha0] at hapos
          exact lt_irrefl _ hapos)
        (ofFinite_ne_infty' a) rfl
    have hane : a ≠ a1 := ne_of_gt ha1
    exact Finset.min'_le _ a (Finset.mem_erase.mpr ⟨hane, haT⟩)

theorem scale_orderings_exists (S : Finset (P1Point ℚ))
    (h0 : P1Point.ofFinite (0 : ℚ) ∈ S) (hinf : P1Point.infty ∈ S)
    (hpos : ∀ p ∈ S, p ≠ P1Point.ofFinite (0 : ℚ) → p ≠ P1Point.infty →
      ∃ x : ℚ, p = P1Point.ofFinite x ∧ 0 < x)
    (hcard : 3 < S.card) : Nonempty (ScaleOrdering S) :=
  ⟨scaleOrdering S h0 hinf hpos hcard⟩

/-- **ScaleOrdering from the paper-conditioned Lemma 2.2 hypotheses** (stage4's
conditioned-∀ consumer can use this directly). -/
noncomputable def scaleOrdering_of_hypotheses (S : Finset (P1Point ℚ))
    (β : P1Point ℚ) (H : Lemma22Hypotheses S β) (hcard : 3 < S.card) :
    ScaleOrdering S :=
  scaleOrdering S H.1 H.2.1 H.2.2.1 hcard

theorem scale_orderings_exists_of_hypotheses (S : Finset (P1Point ℚ))
    (β : P1Point ℚ) (H : Lemma22Hypotheses S β) (hcard : 3 < S.card) :
    Nonempty (ScaleOrdering S) :=
  ⟨scaleOrdering_of_hypotheses S β H hcard⟩

/-- **Separation row extracted from the Lemma 2.2 hypotheses** (stage4 convenience):
if beta = ofFinite b and the paper hypotheses hold, then 2 <= b/a for every positive
finite a in S. -/
theorem hsep_of_hypotheses (S : Finset (P1Point ℚ)) {b : ℚ}
    (H : Lemma22Hypotheses S (P1Point.ofFinite b)) :
    ∀ a : ℚ, P1Point.ofFinite a ∈ S → 0 < a → 2 ≤ b / a := by
  intro a ha hapos
  obtain ⟨a', b', hpa, hpb, hsep⟩ :=
    H.2.2.2.2 (P1Point.ofFinite a) ha
      (by
        intro h
        have ha0 : a = 0 := by simpa [P1Point.ofFinite] using h
        rw [ha0] at hapos
        exact lt_irrefl _ hapos)
      (ofFinite_ne_infty' a)
  have haeq : a = a' := by simpa [P1Point.ofFinite] using hpa
  have hbeq : b = b' := by simpa [P1Point.ofFinite] using hpb
  rw [haeq, hbeq]
  exact hsep

/-- **Fully-hypothesis-driven real-set package** (stage4 convenience): from the
paper-conditioned Lemma 2.2 hypotheses (with beta = ofFinite b), 3 < |S|, the
ScaleOrdering extraction and m,n with r = m/(m+n), the real-set package holds. -/
theorem scale_realHypotheses_exists_of_hypotheses (S : Finset (P1Point ℚ))
    (β : P1Point ℚ) (b : ℚ) (hβ : β = P1Point.ofFinite b)
    (H : Lemma22Hypotheses S β) (hcard : 3 < S.card)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hr : (((scaleOrdering_of_hypotheses S β H hcard).alpha1 /
      (scaleOrdering_of_hypotheses S β H hcard).alpha2 : ℚ) : ℝ) =
        (m : ℝ) / ((m + n : ℕ) : ℝ)) :
    ScaleRealHypotheses S b (scaleOrdering_of_hypotheses S β H hcard)
      (scaleRealS ((scaleOrdering_of_hypotheses S β H hcard).alpha2)⁻¹ S) := by
  subst hβ
  exact scale_realHypotheses_exists S b
    (scaleOrdering_of_hypotheses S (P1Point.ofFinite b) H hcard)
    H.2.2.1 (hsep_of_hypotheses S H) m n hm hn hr

/-- Rows: (scaling component, Lean evidence, status). -/
def gChoiceScaleRows : List (String × String × String) :=
  [ ("scaleP / scaleS (P^1 and finite set scaling)", "scaleP / scaleS (defs)", "DEFINED"),
    ("Lemma 2.2 paper-conditioned hypotheses predicate", "Lemma22Hypotheses", "DEFINED"),
    ("ordering data (two smallest positive finite points + order hypotheses)", "ScaleOrdering + Finset-min extraction scaleOrdering / scale_orderings_exists / scaleOrdering_of_hypotheses (posRatS min'/min'_le)", "PROVED (no fallback needed)"),
    ("0, 1, r = alpha1/alpha2 membership + 0<r<1 after lam = alpha2^{-1}", "scale_memberships_basic", "PROVED"),
    ("full ordering conjunct of the agreed interface", "scale_memberships_full (PROVED; proves scale_memberships_statement)", "PROVED"),
    ("Lemma 2.1 real-set package (0,1,r, m,n, r=m/(m+n), ordering, separation)", "scale_realHypotheses_exists (PROVED) + scaleRatS/scaleRealS + scaleRealS_eq_image/mem lemmas", "PROVED (m,n supplied by stage4's g-choice with hr)"),
    ("g-choice polynomial / chain rule / full Lemma 2.2", "stage4 layers (not re-proved here)", "stage4 scope; no closure claim") ]

theorem gChoiceScaleRows_length : gChoiceScaleRows.length = 7 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1GChoiceScaleActual
end
