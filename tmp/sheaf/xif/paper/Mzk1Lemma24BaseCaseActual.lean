import Mathlib
import tmp.sheaf.xif.paper.Mzk1P1MorphismInterfaceActual

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma24BaseCaseActual

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual

local instance : DecidableEq (P1Point ℚ) := Classical.decEq _

/-- **Lemma 2.4 base case (rational case), PROVED**: if the finite set S consists of
rational points and beta is a rational point outside S, there is a nonconstant
P^1-morphism over Q preserving S into the target set {infinity, 0} and avoiding beta.
(Paper [Mzk1] Lemma 2.4 line 274: reduce to X = P^1; base case m(S)=d(S)=0 is the
rational case.) -/
theorem s3135_base_case_shape (S : Finset ℚ) (β : ℚ) (hβ : β ∉ S) :
    ∃ (φ : P1Morphism ℚ) (targetSet : Set (P1Point ℚ)),
      φ.nonconstant ∧
        PreservesSet φ ((↑(S.image (P1Point.ofFinite (K := ℚ))) : Set (P1Point ℚ))) targetSet ∧
        AvoidsPoint φ (P1Point.ofFinite (K := ℚ) β) targetSet := by
  classical
  let targetSet : Set (P1Point ℚ) :=
    {(P1Point.infty : P1Point ℚ), P1Point.ofFinite (K := ℚ) 0}
  by_cases hS : S.Nonempty
  · let D : ℚ := S.prod (fun s => β - s)
    have hD : D ≠ 0 := by
      unfold D
      apply Finset.prod_ne_zero_iff.mpr
      intro s hs
      exact sub_ne_zero.mpr (fun h => hβ (h ▸ hs))
    let q : Polynomial ℚ :=
      Polynomial.C (2 / D) * S.prod (fun s => Polynomial.X - Polynomial.C s)
    have hqprod_ne : (S.prod (fun s => Polynomial.X - Polynomial.C (R := ℚ) s)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro s _
      exact Polynomial.X_sub_C_ne_zero s
    have hcard : 0 < S.card := hS.card_pos
    have hdeg : q.natDegree = S.card := by
      unfold q
      rw [Polynomial.natDegree_C_mul (by positivity)]
      rw [Polynomial.natDegree_prod _ _ (fun s _ => Polynomial.X_sub_C_ne_zero s)]
      simp
    let mapPoints : P1Point ℚ → P1Point ℚ := fun p => p.map (fun x => Polynomial.eval x q)
    let φ : P1Morphism ℚ :=
      { ratFunc := 0
        mapPoints := mapPoints
        nonconstant := 1 ≤ q.natDegree
        nonconstant_proof := by rw [hdeg]; exact hcard }
    refine ⟨φ, targetSet, ?_, ?_, ?_⟩
    · show 1 ≤ q.natDegree
      rw [hdeg]; exact hcard
    · intro z hz
      obtain ⟨a, haS, rfl⟩ := Finset.mem_image.mp hz
      have hzero : Polynomial.eval a q = 0 := by
        unfold q
        rw [Polynomial.eval_mul, Polynomial.eval_C]
        have hprod : Polynomial.eval a (S.prod (fun s => Polynomial.X - Polynomial.C s)) = 0 := by
          rw [Polynomial.eval_prod]
          exact Finset.prod_eq_zero haS (by simp)
        rw [hprod, mul_zero]
      simp [φ, mapPoints, targetSet, hzero, P1Point.ofFinite, P1Point.infty, Option.map_some]
    · have hDval : Polynomial.eval β (S.prod (fun s => Polynomial.X - Polynomial.C s)) = D := by
        unfold D
        rw [Polynomial.eval_prod]
        apply Finset.prod_congr rfl
        intro s _
        simp
      have hqβ : Polynomial.eval β q = 2 := by
        unfold q
        rw [Polynomial.eval_mul, Polynomial.eval_C, hDval]
        exact div_mul_cancel₀ 2 hD
      intro hmem
      simp only [φ, mapPoints, P1Point.ofFinite, Option.map_some, targetSet, hqβ,
        Set.mem_insert_iff, Set.mem_singleton_iff, P1Point.infty] at hmem
      rcases hmem with h | h
      · exact Option.some_ne_none 2 h
      · exact absurd (Option.some.inj h) (by norm_num)
  · -- empty S: q(x) = x + c with c chosen so that beta + c != 0
    have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    let c : ℚ := if β = -1 then 2 else 1
    let q : Polynomial ℚ := Polynomial.X + Polynomial.C c
    have hqdeg : q.natDegree = 1 := by
      unfold q
      rw [Polynomial.natDegree_X_add_C]
    have hqβ : Polynomial.eval β q ≠ 0 := by
      unfold q c
      split_ifs with h
      · rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
        rw [h]; norm_num
      · rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
        intro hzero
        apply h
        linarith
    let mapPoints : P1Point ℚ → P1Point ℚ := fun p => p.map (fun x => Polynomial.eval x q)
    let φ : P1Morphism ℚ :=
      { ratFunc := 0
        mapPoints := mapPoints
        nonconstant := 1 ≤ q.natDegree
        nonconstant_proof := by omega }
    refine ⟨φ, targetSet, ?_, ?_, ?_⟩
    · show 1 ≤ q.natDegree
      omega
    · intro z hz
      rw [hSempty] at hz
      exact absurd hz (by simp)
    · intro hmem
      simp only [φ, mapPoints, P1Point.ofFinite, Option.map_some, targetSet,
        Set.mem_insert_iff, Set.mem_singleton_iff, P1Point.infty] at hmem
      rcases hmem with h | h
      · exact Option.some_ne_none _ h
      · exact hqβ (Option.some.inj h)

#check s3135_base_case_shape
end LeanFormal.IUT.XiFPaper.Mzk1Lemma24BaseCaseActual
end