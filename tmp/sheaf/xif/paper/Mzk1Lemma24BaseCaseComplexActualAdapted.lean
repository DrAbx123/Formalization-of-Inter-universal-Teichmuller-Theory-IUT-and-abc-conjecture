import Mathlib
import tmp.sheaf.xif.paper.Mzk1P1MorphismInterfaceActual
import LeanFormal.IUT.Audit.Status

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma24BaseCaseComplexActualAdapted

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual

local instance : DecidableEq (P1Point ℂ) := Classical.decEq _

/-- **Lemma 2.4 base case over C, PROVED**: for finite rational S and rational beta not
in S (embedded into C), there is a nonconstant P^1-morphism over C preserving the
embedded S into {infinity, 0} and avoiding the embedded beta.  This is the complex
(rational-case) base provider for the nested induction assembly. -/
theorem s3135_base_case_shape_complex (S : Finset ℚ) (β : ℚ) (hβ : β ∉ S) :
    ∃ (φ : P1Morphism ℂ) (targetSet : Set (P1Point ℂ)),
      φ.nonconstant ∧
        PreservesSet φ
          ((↑(S.image (fun s => P1Point.ofFinite (K := ℂ) ((s : ℚ) : ℂ))) :
            Set (P1Point ℂ))) targetSet ∧
        AvoidsPoint φ (P1Point.ofFinite (K := ℂ) ((β : ℚ) : ℂ)) targetSet := by
  classical
  let targetSet : Set (P1Point ℂ) :=
    {(P1Point.infty : P1Point ℂ), P1Point.ofFinite (K := ℂ) 0}
  have hβc : ((β : ℚ) : ℂ) ∉ S.image (fun s => ((s : ℚ) : ℂ)) := by
    intro h
    obtain ⟨s, hs, hsc⟩ := Finset.mem_image.mp h
    have hsb : s = β := by exact_mod_cast hsc.symm
    exact hβ (hsb ▸ hs)
  by_cases hS : S.Nonempty
  · let D : ℂ := S.prod (fun s => ((β : ℚ) : ℂ) - ((s : ℚ) : ℂ))
    have hD : D ≠ 0 := by
      unfold D
      apply Finset.prod_ne_zero_iff.mpr
      intro s hs
      exact sub_ne_zero.mpr (fun h => by
        have hsb : s = β := by exact_mod_cast h.symm
        exact hβ (hsb ▸ hs))
    let q : Polynomial ℂ :=
      Polynomial.C (2 / D) * S.prod (fun s => Polynomial.X - Polynomial.C ((s : ℚ) : ℂ))
    have hcard : 0 < S.card := hS.card_pos
    have hdeg : q.natDegree = S.card := by
      unfold q
      rw [Polynomial.natDegree_C_mul (by positivity)]
      rw [Polynomial.natDegree_prod _ _ (fun s _ => Polynomial.X_sub_C_ne_zero _)]
      simp
    let mapPoints : P1Point ℂ → P1Point ℂ := fun p => p.map (fun x => Polynomial.eval x q)
    let φ : P1Morphism ℂ :=
      { ratFunc := 0
        mapPoints := mapPoints
        nonconstant := 1 ≤ q.natDegree
        nonconstant_proof := by rw [hdeg]; exact hcard }
    refine ⟨φ, targetSet, ?_, ?_, ?_⟩
    · show 1 ≤ q.natDegree
      rw [hdeg]; exact hcard
    · intro z hz
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hz
      have hzero : Polynomial.eval ((s : ℚ) : ℂ) q = 0 := by
        unfold q
        rw [Polynomial.eval_mul, Polynomial.eval_C]
        have hprod : Polynomial.eval ((s : ℚ) : ℂ)
            (S.prod (fun t => Polynomial.X - Polynomial.C ((t : ℚ) : ℂ))) = 0 := by
          rw [Polynomial.eval_prod]
          exact Finset.prod_eq_zero hs (by simp)
        rw [hprod, mul_zero]
      simp [φ, mapPoints, targetSet, hzero, P1Point.ofFinite, P1Point.infty, Option.map_some]
    · have hDval : Polynomial.eval ((β : ℚ) : ℂ)
          (S.prod (fun s => Polynomial.X - Polynomial.C ((s : ℚ) : ℂ))) = D := by
        unfold D
        rw [Polynomial.eval_prod]
        apply Finset.prod_congr rfl
        intro s _
        simp
      have hqβ : Polynomial.eval ((β : ℚ) : ℂ) q = 2 := by
        unfold q
        rw [Polynomial.eval_mul, Polynomial.eval_C, hDval]
        exact div_mul_cancel₀ 2 hD
      intro hmem
      simp only [φ, mapPoints, P1Point.ofFinite, Option.map_some, targetSet, hqβ,
        Set.mem_insert_iff, Set.mem_singleton_iff, P1Point.infty] at hmem
      rcases hmem with h | h
      · exact Option.some_ne_none 2 h
      · exact absurd (Option.some.inj h) (by norm_num)
  · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    let c : ℂ := if ((β : ℚ) : ℂ) = -1 then 2 else 1
    let q : Polynomial ℂ := Polynomial.X + Polynomial.C c
    have hqdeg : q.natDegree = 1 := by
      unfold q; rw [Polynomial.natDegree_X_add_C]
    have hqβ : Polynomial.eval ((β : ℚ) : ℂ) q ≠ 0 := by
      unfold q c
      split_ifs with h
      · intro hz
        rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] at hz
        have : ((β : ℚ) : ℂ) = -1 := by
          rw [eq_neg_iff_add_eq_zero]
          exact hz
        exact h this
      · intro hz
        rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] at hz
        have : ((β : ℚ) : ℂ) = -1 := by
          rw [eq_neg_iff_add_eq_zero]
          simpa using hz
        exact h this
    let mapPoints : P1Point ℂ → P1Point ℂ := fun p => p.map (fun x => Polynomial.eval x q)
    let φ : P1Morphism ℂ :=
      { ratFunc := 0
        mapPoints := mapPoints
        nonconstant := 1 ≤ q.natDegree
        nonconstant_proof := by rw [hqdeg]; norm_num }
    refine ⟨φ, targetSet, ?_, ?_, ?_⟩
    · show 1 ≤ q.natDegree
      rw [hqdeg]; norm_num
    · intro z hz
      rw [hSempty] at hz
      simp at hz
    · intro hmem
      simp only [φ, mapPoints, P1Point.ofFinite, Option.map_some, targetSet,
        Set.mem_insert_iff, Set.mem_singleton_iff, P1Point.infty] at hmem
      rcases hmem with h | h
      · exact Option.some_ne_none _ h
      · exact hqβ (Option.some.inj h)

#check s3135_base_case_shape_complex
end LeanFormal.IUT.XiFPaper.Mzk1Lemma24BaseCaseComplexActualAdapted
end
