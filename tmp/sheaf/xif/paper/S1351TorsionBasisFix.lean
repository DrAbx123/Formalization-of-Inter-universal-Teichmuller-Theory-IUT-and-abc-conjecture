import tmp.sheaf.xif.paper.S1298TorsionClauseActual
import LeanFormal.IUT.ABCBridge.Galois.EllipticTorsionAlgebraicity

/-!
# S1329: the actual rank-two l-torsion basis, reduced to one exact lemma

S1298TorsionClauseActual fixed the first field of the D5 datum at the concrete
Gaussian arithmetic input as the rank-two l-torsion basis
(Fin 2 -> ZMod l) = E[l].  This file attacks the mathematical core of that
field and records, with proofs, exactly how far the tree gets.

## What is proved here

1. The finiteness half of the S1298 cardinality card is redundant: the single
   numerical equation Nat.card E[l] = l ^ 2 already forces Finite E[l], so the
   first field is equivalent to that one equation (and to finrank = 2), with no
   finiteness input.

2. The exact y-fibre bookkeeping of the division locus over an algebraically
   closed field of characteristic not two: over a root x of prePsi_l the fibre
   of the Weierstrass equation has exactly two points when the value of the
   2-division polynomial Psi_2Sq at x is nonzero, and exactly one point when it
   vanishes.  Hence the number of l-division points is
   1 + 2 * (number of distinct roots), the exact count (the tree previously had
   only the upper bound l ^ 2).

3. Under the group-law criterion l * P = 0 <-> psi_l(P) = 0, the actual
   l-torsion subgroup over the closure is exactly this division locus, so
   Nat.card E[l] = 1 + 2 * #roots; consequently the rank-two basis exists
   exactly when prePsi_l has the full number (l ^ 2 - 1) / 2 of distinct roots.
   This is a sharp reduction of the remaining mathematics to the criterion plus
   the separability/root count of the l-division polynomial.

4. Specialisation to the concrete Gaussian curve: the S1298 projective carrier
   is additively equivalent to the affine one, so the count applies to the
   actual first field.

## What is not proved and not assumed

The group-law criterion for prime l >= 5 is NOT proved here (Mathlib has it
only for n = 2; the tree has it for n = 3, for a different curve and for a
level excluded by PrimeGeFive).  Separability of prePsi_l is likewise not
proved.  Both are explicit hypotheses of the final statements; no basis, no
inhabitant of the criterion, and no separability is asserted.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1329RankTwoTorsionBasisActual

open Polynomial
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1298TorsionClauseActual

local instance s1329GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- Decidable equality on the Gaussian closure, from classical logic. -/
local instance s1329ClosureDecEq (l : PrimeGeFive) :
    DecidableEq (AlgebraicClosure (S1280Arithmetic l).F) :=
  Classical.decEq _

/-! ## 1. The exact target, without any finiteness input -/

/-- The S1298 first field, restated. -/
abbrev S1329TorsionBasis (l : PrimeGeFive) : Type := S1298TorsionBasisType l

/-- Nat.card E[l] = l ^ 2 already forces finiteness: an infinite type has
Nat.card = 0, while l ^ 2 is nonzero. -/
theorem s1329Finite_of_natCard {l : PrimeGeFive}
    (h : Nat.card (S1298TorsionCarrier l) = l.value ^ 2) :
    Finite (S1298TorsionCarrier l) := by
  by_contra hfin
  haveI : Infinite (S1298TorsionCarrier l) := not_finite_iff_infinite.mp hfin
  rw [Nat.card_eq_zero_of_infinite] at h
  exact pow_ne_zero 2 (Nat.Prime.ne_zero l.prime) h.symm

/-- The S1298 cardinality card follows from the bare numerical equation. -/
theorem s1329TorsionCardinalityCard_of_natCard {l : PrimeGeFive}
    (h : Nat.card (S1298TorsionCarrier l) = l.value ^ 2) :
    S1298TorsionCardinalityCard l :=
  ⟨s1329Finite_of_natCard h, h⟩

/-- The exact basis field is equivalent to the bare numerical equation. -/
theorem s1329Basis_nonempty_iff_natCard (l : PrimeGeFive) :
    Nonempty (S1329TorsionBasis l) ↔
      Nat.card (S1298TorsionCarrier l) = l.value ^ 2 := by
  rw [s1298TorsionBasisType_nonempty_iff_cardinalityCard]
  exact ⟨fun h => h.2, fun h => s1329TorsionCardinalityCard_of_natCard h⟩

/-- The exact basis field is equivalent to finrank = 2, with no finiteness
input: an infinite module has finrank zero. -/
theorem s1329Basis_nonempty_iff_finrank (l : PrimeGeFive) :
    Nonempty (S1329TorsionBasis l) ↔
      Module.finrank (ZMod l.value) (S1298TorsionCarrier l) = 2 := by
  constructor
  · rintro ⟨b⟩
    haveI : Finite (S1298TorsionCarrier l) := Finite.of_equiv _ b.toEquiv
    haveI : Module.Finite (ZMod l.value) (S1298TorsionCarrier l) := Module.Finite.of_finite
    exact (s1298TorsionBasisType_iff_finrank_eq_two l).mp ⟨b⟩
  · intro hfr
    haveI : Fact (Nat.Prime l.value) := l.factPrime
    haveI hfin : Module.Finite (ZMod l.value) (S1298TorsionCarrier l) := by
      by_contra h
      rw [Module.finrank_of_not_finite h] at hfr
      exact absurd hfr (by norm_num)
    exact (s1298TorsionBasisType_iff_finrank_eq_two l).mpr hfr

/-! ## 2. The y-fibre of the Weierstrass equation -/

/-- The y-fibre quadratic of the Weierstrass equation at x. -/
def s1329FibreQuadratic {K : Type*} [CommRing K] (W : WeierstrassCurve K) (x : K) : K[X] :=
  X ^ 2 + C (W.a₁ * x + W.a₃) * X + C (-(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆))

section Fibre

variable {K : Type*} [Field K] [DecidableEq K]

/-- The fibre quadratic evaluated is the Weierstrass polynomial difference. -/
theorem s1329FibreQuadratic_eval_eq (W : WeierstrassCurve.Affine K) (x y : K) :
    (s1329FibreQuadratic W x).eval y =
      y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) := by
  simp only [s1329FibreQuadratic, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C]
  ring

/-- Evaluation of the fibre quadratic is the Weierstrass equation. -/
theorem s1329FibreQuadratic_eval_iff (W : WeierstrassCurve.Affine K) (x y : K) :
    (s1329FibreQuadratic W x).eval y = 0 ↔ W.Equation x y := by
  rw [s1329FibreQuadratic_eval_eq, WeierstrassCurve.Affine.equation_iff']

/-- The fibre quadratic is monic. -/
theorem s1329FibreQuadratic_monic (W : WeierstrassCurve.Affine K) (x : K) :
    (s1329FibreQuadratic W x).Monic := by
  rw [s1329FibreQuadratic, add_assoc]
  refine Polynomial.monic_X_pow_add (n := 2) ?_
  have h1 : (C (W.a₁ * x + W.a₃) * X : K[X]).degree ≤ (1 : WithBot Nat) := by
    calc (C (W.a₁ * x + W.a₃) * X : K[X]).degree
        ≤ (C (W.a₁ * x + W.a₃) : K[X]).degree + (X : K[X]).degree :=
          Polynomial.degree_mul_le _ _
      _ ≤ (0 : WithBot Nat) + 1 := add_le_add Polynomial.degree_C_le Polynomial.degree_X_le
      _ = (1 : WithBot Nat) := zero_add 1
  have h0 : (C (-(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) : K[X]).degree ≤ (0 : WithBot Nat) :=
    Polynomial.degree_C_le
  calc (C (W.a₁ * x + W.a₃) * X + C (-(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) : K[X]).degree
      ≤ max (C (W.a₁ * x + W.a₃) * X : K[X]).degree
          (C (-(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) : K[X]).degree :=
        Polynomial.degree_add_le _ _
    _ ≤ max (1 : WithBot Nat) 0 := max_le_max h1 h0
    _ < (2 : WithBot Nat) := by norm_num

/-- The fibre quadratic, completed to a square. -/
theorem s1329FibreQuadratic_eval (W : WeierstrassCurve.Affine K) (x y : K) :
    (s1329FibreQuadratic W x).eval y * 4 =
      (2 * y + W.a₁ * x + W.a₃) ^ 2 - (W.Ψ₂Sq).eval x := by
  rw [WeierstrassCurve.Ψ₂Sq]
  simp only [s1329FibreQuadratic, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆]
  ring

/-- A root of the fibre root finset evaluates to zero. -/
theorem s1329FibreQuadratic_eval_of_mem_roots (W : WeierstrassCurve.Affine K) {x y : K}
    (hy : y ∈ (s1329FibreQuadratic W x).roots.toFinset) :
    (s1329FibreQuadratic W x).eval y = 0 := by
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (s1329FibreQuadratic_monic W x).ne_zero] at hy
  exact hy

/-- A root of the fibre root finset is an equation point. -/
theorem s1329Equation_of_mem_fibre_roots (W : WeierstrassCurve.Affine K) {x y : K}
    (hy : y ∈ (s1329FibreQuadratic W x).roots.toFinset) :
    W.Equation x y :=
  (s1329FibreQuadratic_eval_iff W x y).mp (s1329FibreQuadratic_eval_of_mem_roots W hy)

/-- The fibre quadratic has degree at most two. -/
theorem s1329FibreQuadratic_natDegree_le (W : WeierstrassCurve.Affine K) (x : K) :
    (s1329FibreQuadratic W x).natDegree ≤ 2 := by
  rw [s1329FibreQuadratic, add_assoc]
  have h1 : (C (W.a₁ * x + W.a₃) * X : K[X]).natDegree ≤ 1 := by
    calc (C (W.a₁ * x + W.a₃) * X : K[X]).natDegree
        ≤ (C (W.a₁ * x + W.a₃) : K[X]).natDegree + (X : K[X]).natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ 0 + 1 := by
          refine add_le_add ?_ ?_
          · exact (Polynomial.natDegree_C (W.a₁ * x + W.a₃)).le
          · simp
      _ = 1 := by norm_num
  have h0 : (C (-(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) : K[X]).natDegree ≤ 0 :=
    (Polynomial.natDegree_C (-(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆))).le
  calc (X ^ 2 + (C (W.a₁ * x + W.a₃) * X +
        C (-(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆))) : K[X]).natDegree
      ≤ max ((X ^ 2 : K[X]).natDegree)
          ((C (W.a₁ * x + W.a₃) * X +
            C (-(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) : K[X]).natDegree) :=
        Polynomial.natDegree_add_le _ _
    _ ≤ max 2 1 := max_le_max (by simp)
        ((Polynomial.natDegree_add_le _ _).trans (max_le h1 (h0.trans (by norm_num))))
    _ = 2 := by norm_num

end Fibre
section FibreCard

variable {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K]

/-- The square form of the Weierstrass equation. -/
theorem s1329Equation_iff_sq (W : WeierstrassCurve.Affine K) (h2 : (2 : K) ≠ 0) (x y : K) :
    W.Equation x y ↔ (2 * y + W.a₁ * x + W.a₃) ^ 2 = (W.Ψ₂Sq).eval x := by
  have h4 : (4 : K) ≠ 0 := by
    have h : (4 : K) = 2 * 2 := by norm_num
    rw [h]
    exact mul_ne_zero h2 h2
  have hQ := s1329FibreQuadratic_eval W x y
  have hev := s1329FibreQuadratic_eval_iff W x y
  constructor
  · intro h
    have h0 : (s1329FibreQuadratic W x).eval y = 0 := hev.mpr h
    rw [h0, zero_mul] at hQ
    exact sub_eq_zero.mp hQ.symm
  · intro h
    have h0 : (s1329FibreQuadratic W x).eval y * 4 = 0 := by
      rw [hQ, h]
      ring
    exact hev.mp ((mul_eq_zero.mp h0).resolve_right h4)

/-- The fibre over a root of prePsi_l has exactly two points when the
2-division value is nonzero. -/
theorem s1329FibreQuadratic_roots_card_of_ne_zero (W : WeierstrassCurve.Affine K)
    (h2 : (2 : K) ≠ 0) (x : K) (hc : (W.Ψ₂Sq).eval x ≠ 0) :
    (s1329FibreQuadratic W x).roots.toFinset.card = 2 := by
  classical
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq ((W.Ψ₂Sq).eval x) (by norm_num : 0 < 2)
  have hs0 : s ≠ 0 := by
    intro h
    apply hc
    rw [← hs, h]
    norm_num
  have hsne : s ≠ -s := by
    intro h
    have h2s : (2 : K) * s = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2s with h' | h'
    · exact h2 h'
    · exact hs0 h'
  set y1 : K := (s - (W.a₁ * x + W.a₃)) / 2 with hy1
  set y2 : K := (-s - (W.a₁ * x + W.a₃)) / 2 with hy2
  have h1 : 2 * y1 + W.a₁ * x + W.a₃ = s := by
    rw [hy1]; field_simp; ring
  have h2' : 2 * y2 + W.a₁ * x + W.a₃ = -s := by
    rw [hy2]; field_simp; ring
  have heq1 : W.Equation x y1 := (s1329Equation_iff_sq W h2 x y1).mpr (by rw [h1, hs])
  have heq2 : W.Equation x y2 := (s1329Equation_iff_sq W h2 x y2).mpr (by
    rw [h2', show (-s) ^ 2 = s ^ 2 by ring, hs])
  have hyne : y1 ≠ y2 := by
    intro h
    apply hsne
    have e1 : 2 * y1 + W.a₁ * x + W.a₃ = 2 * y2 + W.a₁ * x + W.a₃ := by rw [h]
    rw [h1, h2'] at e1
    exact e1
  have hmem1 : y1 ∈ (s1329FibreQuadratic W x).roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (s1329FibreQuadratic_monic W x).ne_zero]
    exact (s1329FibreQuadratic_eval_iff W x y1).mpr heq1
  have hmem2 : y2 ∈ (s1329FibreQuadratic W x).roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (s1329FibreQuadratic_monic W x).ne_zero]
    exact (s1329FibreQuadratic_eval_iff W x y2).mpr heq2
  have hsub : ({y1, y2} : Finset K) ⊆ (s1329FibreQuadratic W x).roots.toFinset := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    exacts [hmem1, hmem2]
  have hcard : ({y1, y2} : Finset K).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hyne), Finset.card_singleton]
  have hge : 2 ≤ (s1329FibreQuadratic W x).roots.toFinset.card := by
    calc 2 = ({y1, y2} : Finset K).card := hcard.symm
      _ ≤ _ := Finset.card_le_card hsub
  have hle : (s1329FibreQuadratic W x).roots.toFinset.card ≤ 2 :=
    (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans
      (s1329FibreQuadratic_natDegree_le W x))
  omega

/-- The fibre over a root of prePsi_l has exactly one point when the
2-division value vanishes. -/
theorem s1329FibreQuadratic_roots_card_of_eq_zero (W : WeierstrassCurve.Affine K)
    (h2 : (2 : K) ≠ 0) (x : K) (hc : (W.Ψ₂Sq).eval x = 0) :
    (s1329FibreQuadratic W x).roots.toFinset.card = 1 := by
  classical
  set y0 : K := (-(W.a₁ * x + W.a₃)) / 2 with hy0
  have hy0eq : 2 * y0 + W.a₁ * x + W.a₃ = 0 := by
    rw [hy0]; field_simp; ring
  have hroot : y0 ∈ (s1329FibreQuadratic W x).roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (s1329FibreQuadratic_monic W x).ne_zero]
    exact (s1329FibreQuadratic_eval_iff W x y0).mpr
      ((s1329Equation_iff_sq W h2 x y0).mpr (by rw [hy0eq, hc]; ring))
  have hsub : (s1329FibreQuadratic W x).roots.toFinset ⊆ {y0} := by
    intro y hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (s1329FibreQuadratic_monic W x).ne_zero] at hy
    have heq : W.Equation x y := (s1329FibreQuadratic_eval_iff W x y).mp hy
    have hsq : (2 * y + W.a₁ * x + W.a₃) ^ 2 = 0 := by
      rw [(s1329Equation_iff_sq W h2 x y).mp heq, hc]
    have hz : 2 * y + W.a₁ * x + W.a₃ = 0 := by
      have hsq' : (2 * y + W.a₁ * x + W.a₃) * (2 * y + W.a₁ * x + W.a₃) = 0 := by
        rw [← pow_two]; exact hsq
      exact mul_self_eq_zero.mp hsq'
    have hzero : y = y0 := by
      rw [hy0]
      field_simp
      linear_combination hz
    exact Finset.mem_singleton.mpr hzero
  have hle : (s1329FibreQuadratic W x).roots.toFinset.card ≤ 1 := by
    calc (s1329FibreQuadratic W x).roots.toFinset.card ≤ ({y0} : Finset K).card :=
        Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton _
  have hge : 1 ≤ (s1329FibreQuadratic W x).roots.toFinset.card :=
    Finset.card_pos.mpr ⟨_, hroot⟩
  omega

end FibreCard


/-! ## 3. The division locus, the criterion, and the exact count -/

section Locus

variable {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K]

/-- The group-law criterion: l-torsion is exactly the vanishing locus of
prePsi_l.  This is the exact missing mathematical lemma. -/
def s1329DivisionCriterion (W : WeierstrassCurve.Affine K) (l : Nat) : Prop :=
  ∀ P : W.Point, (l : Int) • P = 0 ↔ W.evalDivisionPolynomialAtPoint (l : Int) P = 0

/-- The x-coordinates of l-division points. -/
def s1329RootFinset (W : WeierstrassCurve.Affine K) (l : Nat) : Finset K :=
  (W.preΨ (l : Int)).roots.toFinset

/-- A root of the x-coordinate root finset evaluates prePsi_l to zero. -/
theorem s1329PreΨ_eval_of_mem_roots (W : WeierstrassCurve.Affine K) {l : Nat}
    (hpre : W.preΨ (l : Int) ≠ 0) {x : K} (hx : x ∈ s1329RootFinset W l) :
    (W.preΨ (l : Int)).eval x = 0 := by
  rw [s1329RootFinset, Multiset.mem_toFinset, Polynomial.mem_roots hpre] at hx
  exact hx

/-- The index type of the l-division locus: a root x and a y over that root. -/
abbrev s1329DivisionIndex (W : WeierstrassCurve.Affine K) (l : Nat) :=
  Sigma fun x : {x : K // x ∈ s1329RootFinset W l} =>
    {y : K // y ∈ (s1329FibreQuadratic W x.1).roots.toFinset}

/-- The actual point attached to a division index. -/
noncomputable def s1329DivisionPoint (W : WeierstrassCurve.Affine K) [W.IsElliptic] (l : Nat)
    (p : s1329DivisionIndex W l) : W.Point :=
  WeierstrassCurve.Affine.Point.mk (W' := W) (s1329Equation_of_mem_fibre_roots W p.2.2)

/-- The l-division locus as a finite set of actual points. -/
noncomputable def s1329DivisionCandidates (W : WeierstrassCurve.Affine K) [W.IsElliptic]
    (l : Nat) : Finset W.Point := by
  classical
  exact insert 0 (Finset.univ.image (s1329DivisionPoint W l))

/-- The index-to-point map is injective. -/
theorem s1329DivisionPoint_injective (W : WeierstrassCurve.Affine K) [W.IsElliptic] (l : Nat) :
    Function.Injective (s1329DivisionPoint W l) := by
  classical
  rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩ heq
  simp only [s1329DivisionPoint, WeierstrassCurve.Affine.Point.mk] at heq
  rw [WeierstrassCurve.Affine.Point.some.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  rfl

/-- The exact cardinality of the l-division locus: one point at infinity plus
two points over each root, when no root is a 2-torsion x-coordinate. -/
theorem s1329DivisionCandidates_card (W : WeierstrassCurve.Affine K) [W.IsElliptic] (l : Nat)
    (h2 : (2 : K) ≠ 0)
    (hΨ : ∀ x ∈ s1329RootFinset W l, (W.Ψ₂Sq).eval x ≠ 0) :
    (s1329DivisionCandidates W l).card = 1 + 2 * (s1329RootFinset W l).card := by
  classical
  have hfib : ∀ x : {x : K // x ∈ s1329RootFinset W l},
      (s1329FibreQuadratic W x.1).roots.toFinset.card = 2 :=
    fun x => s1329FibreQuadratic_roots_card_of_ne_zero W h2 x.1 (hΨ x.1 x.2)
  have hinj : Function.Injective (s1329DivisionPoint W l) := s1329DivisionPoint_injective W l
  have hindex : Nat.card (s1329DivisionIndex W l) = 2 * (s1329RootFinset W l).card := by
    rw [Nat.card_sigma]
    have hterm : ∀ x : {x : K // x ∈ s1329RootFinset W l},
        Nat.card {y : K // y ∈ (s1329FibreQuadratic W x.1).roots.toFinset} = 2 := by
      intro x
      rw [LeanFormal.IUT.IUTII.Frobenioid.Example36.TateModuleProfinite.natCard_subtype_mem_finset]
      exact hfib x
    rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_const, Finset.card_univ,
      Fintype.card_eq_nat_card,
      LeanFormal.IUT.IUTII.Frobenioid.Example36.TateModuleProfinite.natCard_subtype_mem_finset,
      nsmul_eq_mul, Nat.cast_id]
    omega
  have hnotmem : (0 : W.Point) ∉ Finset.univ.image (s1329DivisionPoint W l) := by
    rw [Finset.mem_image]
    rintro ⟨p, -, hp⟩
    have hne : s1329DivisionPoint W l p ≠ 0 := by
      simp only [s1329DivisionPoint, WeierstrassCurve.Affine.Point.mk]
      exact WeierstrassCurve.Affine.Point.some_ne_zero _
    exact hne hp
  have himage : (Finset.univ.image (s1329DivisionPoint W l)).card =
      Nat.card (s1329DivisionIndex W l) := by
    rw [Finset.card_image_of_injective (f := s1329DivisionPoint W l) Finset.univ hinj,
      Finset.card_univ, Fintype.card_eq_nat_card]
  rw [s1329DivisionCandidates, Finset.card_insert_of_notMem hnotmem, himage, hindex]
  omega

/-- Membership in the l-division locus. -/
theorem s1329DivisionCandidates_mem (W : WeierstrassCurve.Affine K) [W.IsElliptic] (l : Nat)
    (P : W.Point) :
    P ∈ s1329DivisionCandidates W l ↔
      P = 0 ∨ ∃ p : s1329DivisionIndex W l, s1329DivisionPoint W l p = P := by
  classical
  rw [s1329DivisionCandidates, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (rfl | ⟨p, -, hp⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨p, hp⟩
  · rintro (rfl | ⟨p, hp⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨p, Finset.mem_univ _, hp⟩

/-- Under the criterion, subgroup membership is locus membership. -/
theorem s1329TorsionBy_mem_iff (W : WeierstrassCurve.Affine K) [W.IsElliptic] (l : Nat)
    (hcrit : s1329DivisionCriterion W l) (hodd : ¬ Even (l : Int))
    (hpre : W.preΨ (l : Int) ≠ 0) (P : W.Point) :
    P ∈ AddSubgroup.torsionBy W.Point (l : Int) ↔ P ∈ s1329DivisionCandidates W l := by
  classical
  constructor
  · intro hP
    have hnsmul : l • P = 0 := (AddSubgroup.torsionBy.nsmul_iff).mp hP
    have hz : (l : Int) • P = 0 := by rw [natCast_zsmul]; exact hnsmul
    have hev : W.evalDivisionPolynomialAtPoint (l : Int) P = 0 := (hcrit P).mp hz
    rcases P with _ | ⟨x, y, hns⟩
    · rw [s1329DivisionCandidates_mem]
      exact Or.inl rfl
    · rw [s1329DivisionCandidates_mem]
      right
      rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_some,
        W.evalDivisionPolynomial_eq_eval_preΨ_of_odd hns.1 hodd] at hev
      have hx : x ∈ s1329RootFinset W l := by
        rw [s1329RootFinset, Multiset.mem_toFinset, Polynomial.mem_roots hpre]
        exact hev
      have hy : y ∈ (s1329FibreQuadratic W x).roots.toFinset := by
        rw [Multiset.mem_toFinset, Polynomial.mem_roots (s1329FibreQuadratic_monic W x).ne_zero]
        exact (s1329FibreQuadratic_eval_iff W x y).mpr hns.1
      refine ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, ?_⟩
      simp only [s1329DivisionPoint, WeierstrassCurve.Affine.Point.mk]
  · intro hP
    rw [s1329DivisionCandidates_mem] at hP
    rcases hP with rfl | ⟨p, rfl⟩
    · exact (AddSubgroup.torsionBy.nsmul_iff).mpr (by simp)
    · rw [AddSubgroup.torsionBy.nsmul_iff]
      have hz : (l : Int) • s1329DivisionPoint W l p = 0 := by
        rw [hcrit]
        rw [s1329DivisionPoint, WeierstrassCurve.Affine.Point.mk,
          WeierstrassCurve.evalDivisionPolynomialAtPoint_some,
          W.evalDivisionPolynomial_eq_eval_preΨ_of_odd
            (s1329Equation_of_mem_fibre_roots W p.2.2) hodd]
        exact s1329PreΨ_eval_of_mem_roots W hpre p.1.2
      simpa [natCast_zsmul] using hz

/-- Under the criterion, the actual l-torsion subgroup is the l-division
locus. -/
theorem s1329TorsionBy_eq_candidates (W : WeierstrassCurve.Affine K) [W.IsElliptic] (l : Nat)
    (hcrit : s1329DivisionCriterion W l) (hodd : ¬ Even (l : Int))
    (hpre : W.preΨ (l : Int) ≠ 0) :
    (AddSubgroup.torsionBy W.Point (l : Int) : Set W.Point) =
      ↑(s1329DivisionCandidates W l) := by
  ext P
  rw [SetLike.mem_coe, Finset.mem_coe]
  exact s1329TorsionBy_mem_iff W l hcrit hodd hpre P

/-- The exact count of the actual l-torsion under the criterion. -/
theorem s1329NatCard_torsionBy_eq (W : WeierstrassCurve.Affine K) [W.IsElliptic] (l : Nat)
    (h2 : (2 : K) ≠ 0) (hcrit : s1329DivisionCriterion W l) (hodd : ¬ Even (l : Int))
    (hpre : W.preΨ (l : Int) ≠ 0)
    (hΨ : ∀ x ∈ s1329RootFinset W l, (W.Ψ₂Sq).eval x ≠ 0) :
    Nat.card (AddSubgroup.torsionBy W.Point (l : Int)) =
      1 + 2 * (s1329RootFinset W l).card := by
  classical
  have hset := s1329TorsionBy_eq_candidates W l hcrit hodd hpre
  have h1 : Nat.card (AddSubgroup.torsionBy W.Point (l : Int)) =
      (s1329DivisionCandidates W l).card := by
    rw [← LeanFormal.IUT.IUTII.Frobenioid.Example36.TateModuleProfinite.natCard_subtype_mem_finset
      (s1329DivisionCandidates W l)]
    exact Nat.card_congr (Equiv.setCongr hset)
  rw [h1, s1329DivisionCandidates_card W l h2 hΨ]

/-- The square of an odd number is odd. -/
theorem s1329Odd_sq {n : Nat} (h : Odd n) : Odd (n ^ 2) := by
  rw [pow_two]
  exact Odd.mul h h

/-- For odd N, the two forms of the root count agree. -/
theorem s1329TwoMulEqDiv {a N : Nat} (hN : Odd N) (h : 2 * a = N - 1) :
    a = (N - 1) / 2 := by
  obtain ⟨k, hk⟩ := hN
  have h2 : N - 1 = 2 * k := by omega
  rw [h2, Nat.mul_div_cancel_left k (by norm_num : 0 < 2)]
  omega

/-- The reverse direction of the two forms of the root count. -/
theorem s1329DivEqTwoMul {a N : Nat} (hN : Odd N) (h : a = (N - 1) / 2) :
    2 * a = N - 1 := by
  obtain ⟨k, hk⟩ := hN
  have h2 : N - 1 = 2 * k := by omega
  rw [h2, Nat.mul_div_cancel_left k (by norm_num : 0 < 2)] at h
  omega

/-- Linear bookkeeping, isolated so that omega never sees a power. -/
theorem s1329TwoMulOfOneAdd {a N : Nat} (h : 1 + 2 * a = N) : 2 * a = N - 1 := by
  omega

/-- Linear bookkeeping, isolated so that omega never sees a power. -/
theorem s1329OneAddTwoMul {a N : Nat} (h : 2 * a = N - 1) (hN : 0 < N) :
    1 + 2 * a = N := by
  omega

/-- Sharp reduction: under the criterion, the actual l-torsion has l ^ 2
elements exactly when prePsi_l has the full number (l ^ 2 - 1) / 2 of distinct
roots. -/
theorem s1329NatCard_eq_sq_iff_separable (W : WeierstrassCurve.Affine K) [W.IsElliptic]
    (l : Nat) (h2 : (2 : K) ≠ 0) (hcrit : s1329DivisionCriterion W l)
    (hodd : ¬ Even (l : Int)) (hpre : W.preΨ (l : Int) ≠ 0)
    (hΨ : ∀ x ∈ s1329RootFinset W l, (W.Ψ₂Sq).eval x ≠ 0) (hoddl : Odd l) :
    Nat.card (AddSubgroup.torsionBy W.Point (l : Int)) = l ^ 2 ↔
      (s1329RootFinset W l).card = (l ^ 2 - 1) / 2 := by
  rw [s1329NatCard_torsionBy_eq W l h2 hcrit hodd hpre hΨ]
  have hN : Odd (l ^ 2) := s1329Odd_sq hoddl
  obtain ⟨k, hk⟩ := hoddl
  have hl0 : 0 < l := by omega
  constructor
  · intro h
    exact s1329TwoMulEqDiv hN (s1329TwoMulOfOneAdd h)
  · intro h
    exact s1329OneAddTwoMul (s1329DivEqTwoMul hN h) (pow_pos hl0 2)

end Locus


/-! ## 4. Specialisation to the concrete Gaussian curve -/

section Concrete

/-- The algebraic closure of the Gaussian field used by the concrete input. -/
abbrev S1329Closure (l : PrimeGeFive) : Type :=
  AlgebraicClosure (S1280Arithmetic l).F

/-- The projective model of the concrete curve over the closure. -/
noncomputable abbrev S1329ProjectiveCurve (l : PrimeGeFive) :
    WeierstrassCurve.Projective (S1329Closure l) :=
  (((S1280Arithmetic l).curve).curve.toProjective).baseChange (S1329Closure l)

/-- The affine model of the concrete curve over the closure. -/
noncomputable abbrev S1329Curve (l : PrimeGeFive) :
    WeierstrassCurve.Affine (S1329Closure l) :=
  ((S1280Arithmetic l).curve).curve.baseChange (S1329Closure l)

/-- Its affine model agrees with the affine model of the projective one. -/
theorem s1329Curve_eq_toAffine (l : PrimeGeFive) :
    (S1329ProjectiveCurve l).toAffine = S1329Curve l :=
  rfl

/-- The concrete curve is elliptic. -/
instance s1329CurveIsElliptic (l : PrimeGeFive) : (S1329Curve l).IsElliptic := by
  show WeierstrassCurve.IsElliptic
    ((((S1280Arithmetic l).curve).curve).map
      (algebraMap (S1280Arithmetic l).F (S1329Closure l)))
  infer_instance

/-- The projective-to-affine additive equivalence of the concrete curve. -/
noncomputable def s1329ProjectiveAffineEquiv (l : PrimeGeFive) :
    (S1329ProjectiveCurve l).Point ≃+ (S1329Curve l).Point :=
  WeierstrassCurve.Projective.Point.toAffineAddEquiv (S1329ProjectiveCurve l)

/-- Torsion is preserved by an additive equivalence, so the cardinalities
agree. -/
theorem s1329NatCard_torsionBy_congr {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (n : Int) :
    Nat.card (AddSubgroup.torsionBy A n) = Nat.card (AddSubgroup.torsionBy B n) := by
  have h : AddSubgroup.torsionBy A n ≃ AddSubgroup.torsionBy B n :=
    { toFun := fun x => ⟨e x.1, by
        have hx : n • x.1 = 0 := x.2
        show n • e x.1 = 0
        rw [← map_zsmul, hx, map_zero]⟩
      invFun := fun y => ⟨e.symm y.1, by
        have hy : n • y.1 = 0 := y.2
        show n • e.symm y.1 = 0
        rw [← map_zsmul, hy, map_zero]⟩
      left_inv := fun x => by ext; simp
      right_inv := fun y => by ext; simp }
  exact Nat.card_congr h

/-- The S1298 projective l-torsion carrier is the affine one. -/
theorem s1329NatCard_carrier_eq (l : PrimeGeFive) :
    Nat.card (S1298TorsionCarrier l) =
      Nat.card (AddSubgroup.torsionBy (S1329Curve l).Point (l.value : Int)) :=
  s1329NatCard_torsionBy_congr (s1329ProjectiveAffineEquiv l) (l.value : Int)

/-- The characteristic-zero closure has 2 nonzero. -/
theorem s1329Concrete_two_ne_zero (l : PrimeGeFive) :
    (2 : S1329Closure l) ≠ 0 := by
  haveI : CharZero (S1329Closure l) := inferInstance
  exact_mod_cast (by norm_num : (2 : Nat) ≠ 0)

/-- The characteristic-zero closure has l nonzero. -/
theorem s1329Concrete_l_ne_zero (l : PrimeGeFive) :
    (l.value : S1329Closure l) ≠ 0 := by
  haveI : CharZero (S1329Closure l) := inferInstance
  exact_mod_cast (Nat.Prime.ne_zero l.prime)

/-- l is odd, as an integer. -/
theorem s1329Concrete_odd_int (l : PrimeGeFive) : ¬ Even (l.value : Int) := by
  rw [Int.even_coe_nat, Nat.not_even_iff_odd]
  exact l.prime.odd_of_ne_two (by have := l.ge_five; omega)

/-- prePsi_l is nonzero at the concrete curve. -/
theorem s1329Concrete_preΨ_ne_zero (l : PrimeGeFive) :
    (S1329Curve l).preΨ (l.value : Int) ≠ 0 :=
  WeierstrassCurve.preΨ_ne_zero (W := S1329Curve l) (by
    simpa using s1329Concrete_l_ne_zero l)

/-- The concrete group-law criterion, as an explicit proposition. -/
abbrev S1329ConcreteCriterion (l : PrimeGeFive) : Prop :=
  s1329DivisionCriterion (S1329Curve l) l.value

/-- The concrete separability/root-count statement. -/
abbrev S1329ConcreteSeparable (l : PrimeGeFive) : Prop :=
  (s1329RootFinset (S1329Curve l) l.value).card = (l.value ^ 2 - 1) / 2

/-- No root of prePsi_l is a 2-torsion x-coordinate.  This follows from the
criterion and the (Mathlib) n = 2 criterion, so it is not an independent
hypothesis. -/
theorem s1329NoTwoTorsionRoots_of_criterion (l : PrimeGeFive)
    (hcrit : S1329ConcreteCriterion l) :
    ∀ x ∈ s1329RootFinset (S1329Curve l) l.value,
      ((S1329Curve l).Ψ₂Sq).eval x ≠ 0 := by
  classical
  intro x hx hc
  obtain ⟨m, hm⟩ := l.prime.odd_of_ne_two (by have := l.ge_five; omega)
  have hodd : ¬ Even (l.value : Int) := s1329Concrete_odd_int l
  have hpre : (S1329Curve l).preΨ (l.value : Int) ≠ 0 := s1329Concrete_preΨ_ne_zero l
  set y0 : S1329Closure l :=
    (-((S1329Curve l).a₁ * x + (S1329Curve l).a₃)) / 2 with hy0
  have hy0eq : 2 * y0 + (S1329Curve l).a₁ * x + (S1329Curve l).a₃ = 0 := by
    rw [hy0]; field_simp; ring
  have hEq : (S1329Curve l).Equation x y0 :=
    (s1329Equation_iff_sq (S1329Curve l) (s1329Concrete_two_ne_zero l) x y0).mpr (by
      rw [hy0eq, hc]; ring)
  have hns : (S1329Curve l).Nonsingular x y0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp hEq
  have hψl : ((S1329Curve l).preΨ (l.value : Int)).eval x = 0 :=
    s1329PreΨ_eval_of_mem_roots (S1329Curve l) hpre hx
  have hltor : (l.value : Int) • WeierstrassCurve.Affine.Point.some x y0 hns = 0 := by
    rw [hcrit]
    rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_some,
      (S1329Curve l).evalDivisionPolynomial_eq_eval_preΨ_of_odd hns.1 hodd]
    exact hψl
  have htwo : (2 : Nat) • WeierstrassCurve.Affine.Point.some x y0 hns = 0 := by
    refine ((S1329Curve l).two_nsmul_eq_zero_iff_evalDivisionPolynomialAtPoint_two_eq_zero _).mpr ?_
    rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_some,
      WeierstrassCurve.evalDivisionPolynomial_two]
    exact hy0eq
  have hltor' : l.value • WeierstrassCurve.Affine.Point.some x y0 hns = 0 := by
    simpa [natCast_zsmul] using hltor
  have hdvd2 : addOrderOf (WeierstrassCurve.Affine.Point.some x y0 hns) ∣ 2 :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr htwo
  have hdvdl : addOrderOf (WeierstrassCurve.Affine.Point.some x y0 hns) ∣ l.value :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr hltor'
  have hcop : Nat.Coprime 2 l.value :=
    (Nat.coprime_primes Nat.prime_two l.prime).mpr (by have := l.ge_five; omega)
  have hone : addOrderOf (WeierstrassCurve.Affine.Point.some x y0 hns) = 1 := by
    have hgcd : addOrderOf (WeierstrassCurve.Affine.Point.some x y0 hns) ∣
        Nat.gcd 2 l.value := Nat.dvd_gcd hdvd2 hdvdl
    rw [hcop] at hgcd
    exact Nat.dvd_one.mp hgcd
  exact WeierstrassCurve.Affine.Point.some_ne_zero hns (AddMonoid.addOrderOf_eq_one_iff.mp hone)

/-- The concrete exact count: under the criterion, the actual l-torsion of the
concrete Gaussian curve has 1 + 2 * #roots elements, where #roots is the number
of distinct roots of prePsi_l in the closure. -/
theorem s1329ConcreteNatCard_eq (l : PrimeGeFive) (hcrit : S1329ConcreteCriterion l) :
    Nat.card (S1298TorsionCarrier l) =
      1 + 2 * (s1329RootFinset (S1329Curve l) l.value).card := by
  classical
  rw [s1329NatCard_carrier_eq]
  exact s1329NatCard_torsionBy_eq (S1329Curve l) l.value
    (s1329Concrete_two_ne_zero l) hcrit (s1329Concrete_odd_int l)
    (s1329Concrete_preΨ_ne_zero l) (s1329NoTwoTorsionRoots_of_criterion l hcrit)

/-- The exact numerical form of the S1298 first field, under the criterion. -/
theorem s1329ConcreteNatCard_eq_sq_iff (l : PrimeGeFive)
    (hcrit : S1329ConcreteCriterion l) :
    Nat.card (S1298TorsionCarrier l) = l.value ^ 2 ↔ S1329ConcreteSeparable l := by
  classical
  rw [s1329ConcreteNatCard_eq l hcrit]
  have hoddl : Odd l.value := l.prime.odd_of_ne_two (by have := l.ge_five; omega)
  have hN : Odd (l.value ^ 2) := s1329Odd_sq hoddl
  have hl0 : 0 < l.value := by have := l.ge_five; omega
  constructor
  · intro h
    exact s1329TwoMulEqDiv hN (s1329TwoMulOfOneAdd h)
  · intro h
    exact s1329OneAddTwoMul (s1329DivEqTwoMul hN h) (pow_pos hl0 2)

/-- **Main conditional theorem.**  If the group-law criterion holds at the
concrete Gaussian curve and prePsi_l has the full number of distinct roots,
then the actual S1298 first field is inhabited: the rank-two l-torsion basis
exists.  Both hypotheses are classical facts about division polynomials that
the tree does not have; neither is assumed unconditionally. -/
theorem s1329ConcreteBasis_of_criterion_and_separable (l : PrimeGeFive)
    (hcrit : S1329ConcreteCriterion l) (hsep : S1329ConcreteSeparable l) :
    Nonempty (S1329TorsionBasis l) := by
  apply (s1329Basis_nonempty_iff_natCard l).mpr
  exact (s1329ConcreteNatCard_eq_sq_iff l hcrit).mpr hsep

/-- **Sharp form.**  Under the concrete criterion, the S1298 first field is
inhabited exactly when prePsi_l is separable in the root-count sense.  Hence
the whole remaining gap of the first field of D5 is exactly two classical
facts: the group-law criterion and the separability of the l-division
polynomial. -/
theorem s1329ConcreteBasis_iff_separable (l : PrimeGeFive)
    (hcrit : S1329ConcreteCriterion l) :
    Nonempty (S1329TorsionBasis l) ↔ S1329ConcreteSeparable l := by
  rw [s1329Basis_nonempty_iff_natCard]
  exact s1329ConcreteNatCard_eq_sq_iff l hcrit

end Concrete

/-! ## 5. Axiom footprint -/

#print axioms s1329Finite_of_natCard
#print axioms s1329Basis_nonempty_iff_natCard
#print axioms s1329Basis_nonempty_iff_finrank
#print axioms s1329FibreQuadratic_roots_card_of_ne_zero
#print axioms s1329FibreQuadratic_roots_card_of_eq_zero
#print axioms s1329Equation_iff_sq
#print axioms s1329DivisionCandidates_card
#print axioms s1329TorsionBy_eq_candidates
#print axioms s1329NatCard_torsionBy_eq
#print axioms s1329NatCard_eq_sq_iff_separable
#print axioms s1329NatCard_carrier_eq
#print axioms s1329NoTwoTorsionRoots_of_criterion
#print axioms s1329ConcreteNatCard_eq
#print axioms s1329ConcreteNatCard_eq_sq_iff
#print axioms s1329ConcreteBasis_of_criterion_and_separable
#print axioms s1329ConcreteBasis_iff_separable

end LeanFormal.IUT.XiFPaper.S1329RankTwoTorsionBasisActual