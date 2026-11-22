/- S2566 comp k=4: G ∣ (T4).comp T1 - T5 -/
import tmp.sheaf.xif.paper.S2554Mod613ChainDataActual
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Field.ZMod

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2566ChainComp1dActual

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

def S4 : (ZMod 613)[X] :=
  C 255 +
  C 202 * X ^ 1 +
  C 89 * X ^ 2 +
  C 313 * X ^ 3 +
  C 241 * X ^ 4 +
  C 254 * X ^ 5 +
  C 234 * X ^ 6 +
  C 310 * X ^ 7 +
  C 241 * X ^ 8 +
  C 152 * X ^ 9 +
  C 202 * X ^ 10 +
  C 390 * X ^ 11 +
  C 6 * X ^ 12 +
  C 163 * X ^ 13 +
  C 519 * X ^ 14 +
  C 43 * X ^ 15 +
  C 520 * X ^ 16 +
  C 348 * X ^ 17 +
  C 320 * X ^ 18 +
  C 3 * X ^ 19 +
  C 110 * X ^ 20 +
  C 585 * X ^ 21 +
  C 513 * X ^ 22 +
  C 287 * X ^ 23 +
  C 584 * X ^ 24 +
  C 344 * X ^ 25 +
  C 301 * X ^ 26 +
  C 295 * X ^ 27 +
  C 170 * X ^ 28 +
  C 28 * X ^ 29 +
  C 172 * X ^ 30 +
  C 13 * X ^ 31 +
  C 210 * X ^ 32 +
  C 175 * X ^ 33 +
  C 191 * X ^ 34 +
  C 338 * X ^ 35 +
  C 338 * X ^ 36 +
  C 438 * X ^ 37 +
  C 608 * X ^ 38 +
  C 264 * X ^ 39 +
  C 552 * X ^ 40 +
  C 229 * X ^ 41 +
  C 311 * X ^ 42 +
  C 71 * X ^ 43 +
  C 67 * X ^ 44 +
  C 532 * X ^ 45 +
  C 102 * X ^ 46 +
  C 434 * X ^ 47 +
  C 69 * X ^ 48 +
  C 39 * X ^ 49 +
  C 268 * X ^ 50 +
  C 461 * X ^ 51 +
  C 42 * X ^ 52 +
  C 574 * X ^ 53 +
  C 308 * X ^ 54 +
  C 110 * X ^ 55 +
  C 470 * X ^ 56 +
  C 252 * X ^ 57 +
  C 140 * X ^ 58 +
  C 389 * X ^ 59 +
  C 119 * X ^ 60 +
  C 547 * X ^ 61 +
  C 246 * X ^ 62 +
  C 570 * X ^ 63 +
  C 6 * X ^ 64 +
  C 409 * X ^ 65 +
  C 384 * X ^ 66 +
  C 476 * X ^ 67 +
  C 437 * X ^ 68 +
  C 54 * X ^ 69 +
  C 254 * X ^ 70 +
  C 499 * X ^ 71 +
  C 254 * X ^ 72 +
  C 236 * X ^ 73 +
  C 572 * X ^ 74 +
  C 199 * X ^ 75 +
  C 313 * X ^ 76 +
  C 489 * X ^ 77 +
  C 164 * X ^ 78 +
  C 518 * X ^ 79 +
  C 553 * X ^ 80 +
  C 324 * X ^ 81 +
  C 509 * X ^ 82 +
  C 126 * X ^ 83 +
  C 316 * X ^ 84 +
  C 371 * X ^ 85 +
  C 514 * X ^ 86 +
  C 324 * X ^ 87 +
  C 471 * X ^ 88 +
  C 202 * X ^ 89 +
  C 339 * X ^ 90 +
  C 93 * X ^ 91 +
  C 608 * X ^ 92 +
  C 526 * X ^ 93 +
  C 32 * X ^ 94 +
  C 329 * X ^ 95 +
  C 426 * X ^ 96 +
  C 218 * X ^ 97 +
  C 217 * X ^ 98 +
  C 611 * X ^ 99 +
  C 166 * X ^ 100 +
  C 94 * X ^ 101 +
  C 596 * X ^ 102 +
  C 231 * X ^ 103 +
  C 59 * X ^ 104 +
  C 499 * X ^ 105 +
  C 167 * X ^ 106 +
  C 143 * X ^ 107 +
  C 69 * X ^ 108 +
  C 528 * X ^ 109

lemma natDegree_G_le : G.natDegree ≤ 12 := by unfold G; compute_degree!
lemma natDegree_T1_le : T1.natDegree ≤ 11 := by unfold T1; compute_degree!
lemma natDegree_T4_le : T4.natDegree ≤ 11 := by unfold T4; compute_degree!
lemma natDegree_T5_le : T5.natDegree ≤ 11 := by unfold T5; compute_degree!
lemma S4_natDegree_le : S4.natDegree ≤ 109 := by unfold S4; compute_degree!

theorem chain4_identity : G * S4 = (T4).comp T1 - T5 := by
  have hL : (G * S4).natDegree ≤ 121 := by
    calc (G * S4).natDegree ≤ G.natDegree + S4.natDegree := natDegree_mul_le
      _ ≤ 12 + 109 := by have h1 := natDegree_G_le; have h2 := S4_natDegree_le; omega
  have hR : ((T4).comp T1 - T5).natDegree ≤ 121 := by
    apply natDegree_sub_le_of_le (m := 121) (n := 121)
    · calc ((T4).comp T1).natDegree ≤ T4.natDegree * T1.natDegree := natDegree_comp_le
        _ ≤ 11 * 11 := by have h1 := natDegree_T4_le; have h2 := natDegree_T1_le; nlinarith
    · have h := natDegree_T5_le; omega
  refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq (G * S4) ((T4).comp T1 - T5)
    (f := pts) pts_injective ?_ ?_
  · intro i
    fin_cases i <;>
      (simp [G, S4, T4, T1, T5, pts, Polynomial.eval_comp]
       decide +revert)
  · simp only [Fintype.card_fin]
    omega

theorem chain_dvd_4 : G ∣ (T4).comp T1 - T5 := ⟨S4, chain4_identity.symm⟩

end LeanFormal.IUT.XiFPaper.S2566ChainComp1dActual
end
