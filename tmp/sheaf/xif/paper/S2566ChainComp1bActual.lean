/- S2566 comp k=2: G ∣ (T2).comp T1 - T3 -/
import tmp.sheaf.xif.paper.S2554Mod613ChainDataActual
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Field.ZMod

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2566ChainComp1bActual

open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual

instance : Fact (Nat.Prime 613) := ⟨by norm_num⟩

def pts (i : Fin 122) : ZMod 613 := ((i : ℕ) : ZMod 613)

lemma pts_injective : Function.Injective pts := by
  intro a b h
  have hv : ((a : ℕ) : ZMod 613).val = ((b : ℕ) : ZMod 613).val := by
    simpa only [pts] using congrArg ZMod.val h
  rw [ZMod.val_natCast, ZMod.val_natCast] at hv
  rw [Nat.mod_eq_of_lt (by have := a.isLt; omega),
    Nat.mod_eq_of_lt (by have := b.isLt; omega)] at hv
  exact Fin.ext hv

def S2 : (ZMod 613)[X] :=
  C 372 +
  C 211 * X ^ 1 +
  C 160 * X ^ 2 +
  C 436 * X ^ 3 +
  C 141 * X ^ 4 +
  C 445 * X ^ 5 +
  C 313 * X ^ 6 +
  C 548 * X ^ 7 +
  C 11 * X ^ 8 +
  C 457 * X ^ 9 +
  C 14 * X ^ 10 +
  C 342 * X ^ 11 +
  C 561 * X ^ 12 +
  C 289 * X ^ 13 +
  C 485 * X ^ 14 +
  C 17 * X ^ 15 +
  C 391 * X ^ 16 +
  C 29 * X ^ 17 +
  C 331 * X ^ 18 +
  C 228 * X ^ 19 +
  C 417 * X ^ 20 +
  C 182 * X ^ 21 +
  C 10 * X ^ 22 +
  C 398 * X ^ 23 +
  C 95 * X ^ 24 +
  C 376 * X ^ 25 +
  C 524 * X ^ 26 +
  C 524 * X ^ 27 +
  C 491 * X ^ 28 +
  C 486 * X ^ 29 +
  C 545 * X ^ 30 +
  C 514 * X ^ 31 +
  C 363 * X ^ 32 +
  C 191 * X ^ 33 +
  C 231 * X ^ 34 +
  C 108 * X ^ 35 +
  C 203 * X ^ 36 +
  C 227 * X ^ 37 +
  C 584 * X ^ 38 +
  C 571 * X ^ 39 +
  C 404 * X ^ 40 +
  C 567 * X ^ 41 +
  C 277 * X ^ 42 +
  C 549 * X ^ 43 +
  C 55 * X ^ 44 +
  C 299 * X ^ 45 +
  C 269 * X ^ 46 +
  C 357 * X ^ 47 +
  C 512 * X ^ 48 +
  C 26 * X ^ 49 +
  C 529 * X ^ 50 +
  C 4 * X ^ 51 +
  C 560 * X ^ 52 +
  C 295 * X ^ 53 +
  C 165 * X ^ 54 +
  C 78 * X ^ 55 +
  C 579 * X ^ 56 +
  C 574 * X ^ 57 +
  C 260 * X ^ 58 +
  C 85 * X ^ 59 +
  C 83 * X ^ 60 +
  C 243 * X ^ 61 +
  C 193 * X ^ 62 +
  C 416 * X ^ 63 +
  C 175 * X ^ 64 +
  C 277 * X ^ 65 +
  C 190 * X ^ 66 +
  C 521 * X ^ 67 +
  C 312 * X ^ 68 +
  C 26 * X ^ 69 +
  C 470 * X ^ 70 +
  C 8 * X ^ 71 +
  C 530 * X ^ 72 +
  C 431 * X ^ 73 +
  C 159 * X ^ 74 +
  C 429 * X ^ 75 +
  C 411 * X ^ 76 +
  C 248 * X ^ 77 +
  C 357 * X ^ 78 +
  C 501 * X ^ 79 +
  C 606 * X ^ 80 +
  C 140 * X ^ 81 +
  C 462 * X ^ 82 +
  C 455 * X ^ 83 +
  C 299 * X ^ 84 +
  C 329 * X ^ 85 +
  C 316 * X ^ 86 +
  C 192 * X ^ 87 +
  C 495 * X ^ 88 +
  C 388 * X ^ 89 +
  C 137 * X ^ 90 +
  C 550 * X ^ 91 +
  C 267 * X ^ 92 +
  C 221 * X ^ 93 +
  C 533 * X ^ 94 +
  C 567 * X ^ 95 +
  C 31 * X ^ 96 +
  C 23 * X ^ 97 +
  C 524 * X ^ 98 +
  C 233 * X ^ 99 +
  C 277 * X ^ 100 +
  C 83 * X ^ 101 +
  C 448 * X ^ 102 +
  C 367 * X ^ 103 +
  C 176 * X ^ 104 +
  C 408 * X ^ 105 +
  C 467 * X ^ 106 +
  C 198 * X ^ 107 +
  C 237 * X ^ 108 +
  C 401 * X ^ 109

lemma natDegree_G_le : G.natDegree ≤ 12 := by unfold G; compute_degree!
lemma natDegree_T1_le : T1.natDegree ≤ 11 := by unfold T1; compute_degree!
lemma natDegree_T2_le : T2.natDegree ≤ 11 := by unfold T2; compute_degree!
lemma natDegree_T3_le : T3.natDegree ≤ 11 := by unfold T3; compute_degree!
lemma S2_natDegree_le : S2.natDegree ≤ 109 := by unfold S2; compute_degree!

theorem chain2_identity : G * S2 = (T2).comp T1 - T3 := by
  have hL : (G * S2).natDegree ≤ 121 := by
    calc (G * S2).natDegree ≤ G.natDegree + S2.natDegree := natDegree_mul_le
      _ ≤ 12 + 109 := by have h1 := natDegree_G_le; have h2 := S2_natDegree_le; omega
  have hR : ((T2).comp T1 - T3).natDegree ≤ 121 := by
    apply natDegree_sub_le_of_le (m := 121) (n := 121)
    · calc ((T2).comp T1).natDegree ≤ T2.natDegree * T1.natDegree := natDegree_comp_le
        _ ≤ 11 * 11 := by have h1 := natDegree_T2_le; have h2 := natDegree_T1_le; nlinarith
    · have h := natDegree_T3_le; omega
  refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq (G * S2) ((T2).comp T1 - T3)
    (f := pts) pts_injective ?_ ?_
  · intro i
    fin_cases i <;>
      (simp [G, S2, T2, T1, T3, pts, Polynomial.eval_comp]
       decide +revert)
  · simp only [Fintype.card_fin]
    omega

theorem chain_dvd_2 : G ∣ (T2).comp T1 - T3 := ⟨S2, chain2_identity.symm⟩

end LeanFormal.IUT.XiFPaper.S2566ChainComp1bActual
end
