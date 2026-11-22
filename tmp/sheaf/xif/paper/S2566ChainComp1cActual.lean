/- S2566 comp k=3: G ∣ (T3).comp T1 - T4 -/
import tmp.sheaf.xif.paper.S2554Mod613ChainDataActual
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Field.ZMod

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2566ChainComp1cActual

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

def S3 : (ZMod 613)[X] :=
  C 603 +
  C 585 * X ^ 1 +
  C 125 * X ^ 2 +
  C 77 * X ^ 3 +
  C 322 * X ^ 4 +
  C 61 * X ^ 5 +
  C 411 * X ^ 6 +
  C 597 * X ^ 7 +
  C 381 * X ^ 8 +
  C 114 * X ^ 9 +
  C 119 * X ^ 10 +
  C 492 * X ^ 11 +
  C 342 * X ^ 12 +
  C 597 * X ^ 13 +
  C 205 * X ^ 14 +
  C 475 * X ^ 15 +
  C 50 * X ^ 16 +
  C 154 * X ^ 17 +
  C 540 * X ^ 18 +
  C 506 * X ^ 19 +
  C 525 * X ^ 20 +
  C 83 * X ^ 21 +
  C 433 * X ^ 22 +
  C 609 * X ^ 23 +
  C 190 * X ^ 24 +
  C 582 * X ^ 25 +
  C 367 * X ^ 26 +
  C 155 * X ^ 27 +
  C 175 * X ^ 28 +
  C 409 * X ^ 29 +
  C 430 * X ^ 30 +
  C 328 * X ^ 31 +
  C 271 * X ^ 32 +
  C 529 * X ^ 33 +
  C 389 * X ^ 34 +
  C 577 * X ^ 35 +
  C 311 * X ^ 36 +
  C 238 * X ^ 37 +
  C 31 * X ^ 38 +
  C 584 * X ^ 39 +
  C 64 * X ^ 40 +
  C 29 * X ^ 41 +
  C 516 * X ^ 42 +
  C 545 * X ^ 43 +
  C 476 * X ^ 44 +
  C 31 * X ^ 45 +
  C 601 * X ^ 46 +
  C 451 * X ^ 47 +
  C 583 * X ^ 48 +
  C 186 * X ^ 49 +
  C 543 * X ^ 50 +
  C 406 * X ^ 51 +
  C 239 * X ^ 52 +
  C 157 * X ^ 53 +
  C 557 * X ^ 54 +
  C 456 * X ^ 55 +
  C 47 * X ^ 56 +
  C 331 * X ^ 57 +
  C 446 * X ^ 58 +
  C 38 * X ^ 59 +
  C 545 * X ^ 60 +
  C 338 * X ^ 61 +
  C 562 * X ^ 62 +
  C 212 * X ^ 63 +
  C 113 * X ^ 64 +
  C 568 * X ^ 65 +
  C 251 * X ^ 66 +
  C 186 * X ^ 67 +
  C 503 * X ^ 68 +
  C 177 * X ^ 69 +
  C 228 * X ^ 70 +
  C 499 * X ^ 71 +
  C 214 * X ^ 72 +
  C 601 * X ^ 73 +
  C 204 * X ^ 74 +
  C 141 * X ^ 75 +
  C 124 * X ^ 76 +
  C 483 * X ^ 77 +
  C 52 * X ^ 78 +
  C 404 * X ^ 79 +
  C 61 * X ^ 80 +
  C 137 * X ^ 81 +
  C 544 * X ^ 82 +
  C 456 * X ^ 83 +
  C 187 * X ^ 84 +
  C 444 * X ^ 85 +
  C 596 * X ^ 86 +
  C 505 * X ^ 87 +
  C 470 * X ^ 88 +
  C 526 * X ^ 89 +
  C 376 * X ^ 90 +
  C 104 * X ^ 91 +
  C 594 * X ^ 92 +
  C 101 * X ^ 93 +
  C 336 * X ^ 94 +
  C 405 * X ^ 95 +
  C 419 * X ^ 96 +
  C 367 * X ^ 97 +
  C 445 * X ^ 98 +
  C 563 * X ^ 99 +
  C 472 * X ^ 100 +
  C 511 * X ^ 101 +
  C 188 * X ^ 102 +
  C 258 * X ^ 103 +
  C 249 * X ^ 104 +
  C 215 * X ^ 105 +
  C 497 * X ^ 106 +
  C 510 * X ^ 107 +
  C 499 * X ^ 108 +
  C 327 * X ^ 109

lemma natDegree_G_le : G.natDegree ≤ 12 := by unfold G; compute_degree!
lemma natDegree_T1_le : T1.natDegree ≤ 11 := by unfold T1; compute_degree!
lemma natDegree_T3_le : T3.natDegree ≤ 11 := by unfold T3; compute_degree!
lemma natDegree_T4_le : T4.natDegree ≤ 11 := by unfold T4; compute_degree!
lemma S3_natDegree_le : S3.natDegree ≤ 109 := by unfold S3; compute_degree!

theorem chain3_identity : G * S3 = (T3).comp T1 - T4 := by
  have hL : (G * S3).natDegree ≤ 121 := by
    calc (G * S3).natDegree ≤ G.natDegree + S3.natDegree := natDegree_mul_le
      _ ≤ 12 + 109 := by have h1 := natDegree_G_le; have h2 := S3_natDegree_le; omega
  have hR : ((T3).comp T1 - T4).natDegree ≤ 121 := by
    apply natDegree_sub_le_of_le (m := 121) (n := 121)
    · calc ((T3).comp T1).natDegree ≤ T3.natDegree * T1.natDegree := natDegree_comp_le
        _ ≤ 11 * 11 := by have h1 := natDegree_T3_le; have h2 := natDegree_T1_le; nlinarith
    · have h := natDegree_T4_le; omega
  refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq (G * S3) ((T3).comp T1 - T4)
    (f := pts) pts_injective ?_ ?_
  · intro i
    fin_cases i <;>
      (simp [G, S3, T3, T1, T4, pts, Polynomial.eval_comp]
       decide +revert)
  · simp only [Fintype.card_fin]
    omega

theorem chain_dvd_3 : G ∣ (T3).comp T1 - T4 := ⟨S3, chain3_identity.symm⟩

end LeanFormal.IUT.XiFPaper.S2566ChainComp1cActual
end
