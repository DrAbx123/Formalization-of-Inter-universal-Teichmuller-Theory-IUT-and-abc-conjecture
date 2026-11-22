import tmp.sheaf.xif.paper.Mzk1G1PsiM2ProducerActual
import Mathlib.Tactic

/-!
# ⑥ M2 core layer: algebraic points, the recursion measure, and rational transport

Route §4.3 L304-317 runs the nested induction on the ALGEBRAIC-point layer of P^1
(monic minimal polynomials over Q), because P1Point Q only covers degree-one points while
Branch(psi) contains non-rational algebraic points.

This file supplies the layer below the recursion producer.  It deliberately introduces NO
conditional interface and does NOT restate or modify the route object.

1. isRatPoint (rationality of an algebraic point) with the degree-one characterisation
   isRatPoint p ↔ p.deg = 1 for monic minimal polynomials, and the value ratVal.
2. The lexicographic descent interface muMeasure_lex_of_max_dec,
   muMeasure_lex_of_sum_dec on the pure measure pair N x N.
3. The combinatorial descent lemma muMeasure_lex_of_entry_dec: a single strict decrease
   of one redDeg entry with all other entries unchanged strictly decreases (max, sum)
   lexicographically.  It is proved from the list decompositions foldr_max_append and
   foldr_add_append together with lex_max_sum_of_single_dec.
4. The terminating transport ofRat_transport : isRatPoint (AlgPoint.ofRat c) and
   ratToP1 : P1Point Q, with the consistency ratToP1 (ofRat c) = ofFinite c.

Fallback note (route §4.3 L304-317 safety net): the analytic content of the route steps
(Cauchy root bound and the rational Möbius choice producing the next polynomial h) is
NOT asserted here.  No Mzk1Lemma24Target instance for non-rational beta, and no
hypothesis standing in for that construction, is introduced.  The present layer stops at
the verified combinatorial descent and at the transport to the degree-one layer, on which
the M1 base case mzk1Lemma24Target_of_finite applies.  Nothing below is conditional.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiM2CoreActual

open LeanFormal.IUT.XiFPaper.Mzk1G1PsiM2ProducerActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual

/-! ## 1. Rational algebraic points -/

/-- An algebraic point is rational (lies in P^1(Q)) if its monic minimal polynomial is
the degree-one polynomial X - C c for some c : Q. -/
def isRatPoint (p : AlgPoint) : Prop :=
  ∃ c : ℚ, p.minpoly = Polynomial.X - Polynomial.C c

/-- The finite value of an algebraic point, read off from the constant coefficient:
for minpoly = X - C c this is c. -/
def ratVal (p : AlgPoint) : ℚ := -p.minpoly.coeff 0

/-- Rational algebraic points have degree one. -/
theorem isRatPoint_deg_eq_one {p : AlgPoint} (h : isRatPoint p) : p.deg = 1 := by
  obtain ⟨c, hc⟩ := h
  show p.minpoly.natDegree = 1
  rw [hc, Polynomial.natDegree_X_sub_C]

/-- Conversely, a monic minimal polynomial of degree one is X - C c. -/
theorem isRatPoint_of_deg_eq_one {p : AlgPoint} (hp : p.deg = 1) : isRatPoint p := by
  have hnd : p.minpoly.natDegree = 1 := hp
  have hpoly : p.minpoly = Polynomial.X + Polynomial.C (p.minpoly.coeff 0) :=
    Polynomial.Monic.eq_X_add_C p.monic hnd
  refine ⟨-p.minpoly.coeff 0, hpoly.trans ?_⟩
  rw [Polynomial.C_neg, sub_neg_eq_add]

/-- **Degree-one characterisation.**  For monic minimal polynomials, being rational is
exactly having degree one. -/
theorem isRatPoint_iff_deg_eq_one (p : AlgPoint) : isRatPoint p ↔ p.deg = 1 :=
  ⟨fun h => isRatPoint_deg_eq_one h, fun h => isRatPoint_of_deg_eq_one h⟩

/-- The same statement for the redDeg component of the recursion measure. -/
theorem isRatPoint_redDeg_eq_one {p : AlgPoint} (h : isRatPoint p) : p.redDeg = 1 := by
  show p.minpoly.natDegree = 1
  exact isRatPoint_deg_eq_one h

/-- The value read off from X - C c is c. -/
theorem ratVal_ofRat (c : ℚ) : ratVal (AlgPoint.ofRat c) = c := by
  simp [ratVal, AlgPoint.ofRat, Polynomial.coeff_X_zero, Polynomial.coeff_C]

/-! ## 2. The lexicographic descent interface on the measure -/

/-- If the first component strictly decreases, the measure descends lexicographically. -/
theorem muMeasure_lex_of_max_dec (a b : ℕ × ℕ) (h : a.1 < b.1) :
    Prod.Lex (· < ·) (· < ·) a b :=
  Prod.lex_def.mpr (Or.inl h)

/-- If the first components agree and the second strictly decreases, the measure descends
lexicographically. -/
theorem muMeasure_lex_of_sum_dec (a b : ℕ × ℕ) (h₁ : a.1 = b.1) (h₂ : a.2 < b.2) :
    Prod.Lex (· < ·) (· < ·) a b :=
  Prod.lex_def.mpr (Or.inr ⟨h₁, h₂⟩)

/-! ## 3. The combinatorial descent lemma for the list measure -/

/-- foldr max 0 decomposes over concatenation. -/
theorem foldr_max_append (l₁ l₂ : List ℕ) :
    (l₁ ++ l₂).foldr max 0 = max (l₁.foldr max 0) (l₂.foldr max 0) := by
  induction l₁ with
  | nil => simp
  | cons a l ih => simp [ih, max_assoc]

/-- foldr (· + ·) 0 decomposes over concatenation. -/
theorem foldr_add_append (l₁ l₂ : List ℕ) :
    (l₁ ++ l₂).foldr (· + ·) 0 = l₁.foldr (· + ·) 0 + l₂.foldr (· + ·) 0 := by
  induction l₁ with
  | nil => simp
  | cons a l ih => simp [ih, Nat.add_assoc]

/-- **Single-entry descent (pure list form).**  If one entry x of a list of natural
numbers is replaced by a strictly smaller entry y and all other entries are unchanged,
then the pair (max, sum) strictly decreases lexicographically.  The entry is presented
as pre ++ x :: post. -/
theorem lex_max_sum_of_single_dec (pre post : List ℕ) {y x : ℕ} (hyx : y < x) :
    Prod.Lex (· < ·) (· < ·)
      ((pre ++ y :: post).foldr max 0, (pre ++ y :: post).foldr (· + ·) 0)
      ((pre ++ x :: post).foldr max 0, (pre ++ x :: post).foldr (· + ·) 0) := by
  have hy : max y (post.foldr max 0) ≤ max x (post.foldr max 0) := by
    rw [max_le_iff]
    exact ⟨le_trans hyx.le (le_max_left _ _), le_max_right _ _⟩
  have hM : (pre ++ y :: post).foldr max 0 ≤ (pre ++ x :: post).foldr max 0 := by
    rw [foldr_max_append, foldr_max_append]
    exact max_le_max (le_refl _) hy
  rcases lt_or_eq_of_le hM with hlt | heq
  · exact Prod.lex_def.mpr (Or.inl hlt)
  · refine Prod.lex_def.mpr (Or.inr ⟨heq, ?_⟩)
    show (pre ++ y :: post).foldr (· + ·) 0 < (pre ++ x :: post).foldr (· + ·) 0
    rw [foldr_add_append, foldr_add_append]
    show pre.foldr (· + ·) 0 + (y + post.foldr (· + ·) 0) <
      pre.foldr (· + ·) 0 + (x + post.foldr (· + ·) 0)
    exact Nat.add_lt_add_left (Nat.add_lt_add_right hyx (post.foldr (· + ·) 0))
      (pre.foldr (· + ·) 0)

/-- The recursion measure of a list of algebraic points: (max redDeg, sum redDeg). -/
def muList (l : List AlgPoint) : ℕ × ℕ :=
  (l.foldr (fun p m => max p.redDeg m) 0, l.foldr (fun p s => p.redDeg + s) 0)

/-- muMeasure S beta is the list measure of beta :: S (definitional). -/
theorem muMeasure_eq_muList (S : List AlgPoint) (β : AlgPoint) :
    muMeasure S β = muList (β :: S) := rfl

/-- muList is the (max, sum) of the list of reduced degrees. -/
theorem muList_eq_map (l : List AlgPoint) :
    muList l = ((l.map AlgPoint.redDeg).foldr max 0,
      (l.map AlgPoint.redDeg).foldr (· + ·) 0) := by
  simp only [muList, List.foldr_map]

/-- **Single-entry descent for algebraic points.**  Replacing one point p of a list by a
point q of strictly smaller redDeg, leaving all other points unchanged, strictly
decreases the list measure (max, sum) lexicographically. -/
theorem muList_lex_of_entry_dec (pre post : List AlgPoint) {p q : AlgPoint}
    (h : q.redDeg < p.redDeg) :
    Prod.Lex (· < ·) (· < ·) (muList (pre ++ q :: post)) (muList (pre ++ p :: post)) := by
  rw [muList_eq_map, muList_eq_map]
  simp only [List.map_append, List.map_cons]
  exact lex_max_sum_of_single_dec (pre.map AlgPoint.redDeg) (post.map AlgPoint.redDeg) h

/-- **Single-entry descent for muMeasure.**  If one point of S is replaced by a point
of strictly smaller redDeg while the protected point beta and all other points stay
unchanged, then muMeasure S beta strictly decreases lexicographically. -/
theorem muMeasure_lex_of_entry_dec (β : AlgPoint) (pre post : List AlgPoint) {p q : AlgPoint}
    (h : q.redDeg < p.redDeg) :
    Prod.Lex (· < ·) (· < ·) (muMeasure (pre ++ q :: post) β)
      (muMeasure (pre ++ p :: post) β) := by
  rw [muMeasure_eq_muList, muMeasure_eq_muList]
  exact muList_lex_of_entry_dec (β :: pre) post h

/-- The protected point beta itself may be the entry whose redDeg decreases. -/
theorem muMeasure_lex_of_beta_dec (S : List AlgPoint) {β γ : AlgPoint}
    (h : γ.redDeg < β.redDeg) :
    Prod.Lex (· < ·) (· < ·) (muMeasure S γ) (muMeasure S β) := by
  rw [muMeasure_eq_muList, muMeasure_eq_muList]
  exact muList_lex_of_entry_dec [] S h

/-! ## 4. Terminating transport to the degree-one layer -/

/-- **Transport.**  The rational point c is a rational algebraic point. -/
theorem ofRat_transport (c : ℚ) : isRatPoint (AlgPoint.ofRat c) :=
  ⟨c, rfl⟩

/-- The rational value read off from the constant coefficient equals the chosen witness. -/
theorem ratVal_eq_choose {p : AlgPoint} (h : isRatPoint p) :
    ratVal p = Classical.choose h := by
  have hcoeff : p.minpoly.coeff 0 = -(Classical.choose h) := by
    simpa using congrArg (fun q : Polynomial ℚ => q.coeff 0) (Classical.choose_spec h)
  simp [ratVal, hcoeff]

/-- **The transport map to P^1(Q).**  A rational algebraic point is sent to the finite
point of P^1(Q) encoded by its witness. -/
def ratToP1 (p : AlgPoint) (h : isRatPoint p) : P1Point ℚ :=
  P1Point.ofFinite (Classical.choose h)

/-- ratToP1 depends only on the value ratVal, i.e. on the constant coefficient of the
minimal polynomial, not on the particular witness chosen. -/
theorem ratToP1_eq_ofFinite_ratVal (p : AlgPoint) (h : isRatPoint p) :
    ratToP1 p h = P1Point.ofFinite (ratVal p) := by
  unfold ratToP1
  exact congrArg P1Point.ofFinite (ratVal_eq_choose h).symm

/-- The transport of a rational point is the expected finite point. -/
theorem ratToP1_ofRat (c : ℚ) :
    ratToP1 (AlgPoint.ofRat c) (ofRat_transport c) = P1Point.ofFinite c := by
  rw [ratToP1_eq_ofFinite_ratVal, ratVal_ofRat]

/-! ## Axiom audit -/

#print axioms isRatPoint
#print axioms ratVal
#print axioms isRatPoint_deg_eq_one
#print axioms isRatPoint_of_deg_eq_one
#print axioms isRatPoint_iff_deg_eq_one
#print axioms isRatPoint_redDeg_eq_one
#print axioms ratVal_ofRat
#print axioms muMeasure_lex_of_max_dec
#print axioms muMeasure_lex_of_sum_dec
#print axioms foldr_max_append
#print axioms foldr_add_append
#print axioms lex_max_sum_of_single_dec
#print axioms muList
#print axioms muMeasure_eq_muList
#print axioms muList_eq_map
#print axioms muList_lex_of_entry_dec
#print axioms muMeasure_lex_of_entry_dec
#print axioms muMeasure_lex_of_beta_dec
#print axioms ofRat_transport
#print axioms ratVal_eq_choose
#print axioms ratToP1
#print axioms ratToP1_eq_ofFinite_ratVal
#print axioms ratToP1_ofRat

end LeanFormal.IUT.XiFPaper.Mzk1G1PsiM2CoreActual
