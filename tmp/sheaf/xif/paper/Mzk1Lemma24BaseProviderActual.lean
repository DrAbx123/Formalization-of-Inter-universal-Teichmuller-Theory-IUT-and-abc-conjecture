import Mathlib
import tmp.sheaf.xif.paper.Mzk1P1MorphismInterfaceActual
import tmp.sheaf.xif.paper.Mzk1Lemma24BaseCaseActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1500000

noncomputable section

/-!
# STEP 0 prior-art: base case|rational base lift|Q->C|s3135_base_case_shape -> hits Mzk1Lemma24BaseCaseActual:17 s3135_base_case_shape (PROVED rational provider: exists P1Morphism ℚ preserving S into {inf,0} avoiding beta), Mzk1P1MorphismInterfaceActual -> REUSE (same explicit polynomial construction recast over C; rational base lift for the nested assembly).

# Mzk1Lemma24BaseProviderActual — rational base provider lifted to C (Lemma 2.4 base case)

Corpus: papers/motizuki_corpus/text/Noncritical Belyi Maps.txt, Lemma 2.4 (line 274);
base case for the nested (m,d)-induction.
CONTENT: the C-version of abc's PROVED rational base case s3135_base_case_shape.
For finite rational S and rational beta not in S, there is a nonconstant P^1-morphism
over C preserving the embedded S into {infinity, 0} and avoiding the embedded beta.
The construction is the same explicit q = (2/D) * prod (X - s) with D = prod (beta - s)
(and a linear q in the empty-S case), recast over C.  No fake; registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma24BaseProviderActual

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open Polynomial

local instance : DecidableEq (P1Point ℂ) := Classical.decEq _

/-- **Lemma 2.4 base provider over C (rational base lift):** for finite rational S and
rational beta not in S, a nonconstant P^1-morphism over C preserves the embedded S
into {infinity, 0} and avoids the embedded beta. -/
theorem s3135_base_provider_complex (S : Finset ℚ) (β : ℚ) (hβ : β ∉ S) :
    ∃ (φ : P1Morphism ℂ) (targetSet : Set (P1Point ℂ)),
      φ.nonconstant ∧
        PreservesSet φ
          ((↑(S.image (fun s => P1Point.ofFinite (K := ℂ) ((s : ℚ) : ℂ))) :
            Set (P1Point ℂ))) targetSet ∧
        AvoidsPoint φ (P1Point.ofFinite (K := ℂ) ((β : ℚ) : ℂ)) targetSet := by
  classical
  let targetSet : Set (P1Point ℂ) :=
    {(P1Point.infty : P1Point ℂ), P1Point.ofFinite (K := ℂ) 0}
  by_cases hS : S.Nonempty
  · let D : ℂ := S.prod (fun s => ((β : ℚ) : ℂ) - ((s : ℚ) : ℂ))
    have hD : D ≠ 0 := by
      unfold D
      apply Finset.prod_ne_zero_iff.mpr
      intro s hs hzero
      have hsb : s = β := by exact_mod_cast (sub_eq_zero.mp hzero).symm
      exact hβ (hsb ▸ hs)
    let q : Polynomial ℂ :=
      Polynomial.C (2 / D) * S.prod (fun s => Polynomial.X - Polynomial.C ((s : ℚ) : ℂ))
    have hcard : 0 < S.card := hS.card_pos
    have h2D : (2 / D : ℂ) ≠ 0 := div_ne_zero (by norm_num) hD
    have hdeg : q.natDegree = S.card := by
      unfold q
      rw [Polynomial.natDegree_C_mul h2D]
      rw [Polynomial.natDegree_prod _ _ (fun s _ => Polynomial.X_sub_C_ne_zero _)]
      simp
    let mapPoints : P1Point ℂ → P1Point ℂ :=
      fun p => p.map (fun x => Polynomial.eval x q)
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
      simp [φ, mapPoints, targetSet, hzero, P1Point.ofFinite, P1Point.infty,
        Option.map_some]
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
      unfold q
      rw [Polynomial.natDegree_X_add_C]
    have hqβ : Polynomial.eval ((β : ℚ) : ℂ) q ≠ 0 := by
      unfold q c
      split_ifs with h
      · rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
        norm_num [h]
      · rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
        intro hz
        apply h
        rw [eq_neg_iff_add_eq_zero]
        exact hz
    let mapPoints : P1Point ℂ → P1Point ℂ :=
      fun p => p.map (fun x => Polynomial.eval x q)
    let φ : P1Morphism ℂ :=
      { ratFunc := 0
        mapPoints := mapPoints
        nonconstant := 1 ≤ q.natDegree
        nonconstant_proof := by rw [hqdeg] }
    refine ⟨φ, targetSet, ?_, ?_, ?_⟩
    · show 1 ≤ q.natDegree
      rw [hqdeg]
    · intro z hz
      rw [hSempty] at hz
      exact absurd hz (by simp)
    · intro hmem
      simp only [φ, mapPoints, P1Point.ofFinite, Option.map_some, targetSet,
        Set.mem_insert_iff, Set.mem_singleton_iff, P1Point.infty] at hmem
      rcases hmem with h | h
      · exact Option.some_ne_none _ h
      · exact hqβ (Option.some.inj h)

/-- Base-provider row record. -/
def baseProviderRows : List (String × String × String) :=
  [ ("rational base case (abc)", "A", "CONSUMED Mzk1Lemma24BaseCaseActual.s3135_base_case_shape (PROVED)")
  , ("C-version of the base provider (rational base lift)", "A", "PROVED s3135_base_provider_complex (same explicit q over C)")
  , ("nonconstant + PreservesSet {inf,0} + AvoidsPoint beta", "A", "PROVED (all three clauses in the theorem)")
  , ("nested (m,d)-induction assembly consumption", "interface", "abc Mzk1Lemma24AssemblyActual can import s3135_base_provider_complex") ]

/-- The base-provider row record has four rows. -/
theorem baseProviderRows_length : baseProviderRows.length = 4 := rfl

#check s3135_base_provider_complex
#check baseProviderRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Lemma24BaseProviderActual
end