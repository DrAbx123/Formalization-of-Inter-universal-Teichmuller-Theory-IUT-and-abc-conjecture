/- S2566 comp k=1: G ∣ (T1).comp T1 - T2 -/
import tmp.sheaf.xif.paper.S2554Mod613ChainDataActual
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Field.ZMod

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2566ChainComp1aActual

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

def S1 : (ZMod 613)[X] :=
  C 309 +
  C 441 * X ^ 1 +
  C 172 * X ^ 2 +
  C 353 * X ^ 3 +
  C 585 * X ^ 4 +
  C 592 * X ^ 5 +
  C 299 * X ^ 6 +
  C 559 * X ^ 7 +
  C 301 * X ^ 8 +
  C 556 * X ^ 9 +
  C 107 * X ^ 10 +
  C 364 * X ^ 11 +
  C 229 * X ^ 12 +
  C 119 * X ^ 13 +
  C 31 * X ^ 14 +
  C 442 * X ^ 15 +
  C 200 * X ^ 16 +
  C 155 * X ^ 17 +
  C 410 * X ^ 18 +
  C 380 * X ^ 19 +
  C 503 * X ^ 20 +
  C 329 * X ^ 21 +
  C 318 * X ^ 22 +
  C 228 * X ^ 23 +
  C 274 * X ^ 24 +
  C 559 * X ^ 25 +
  C 207 * X ^ 26 +
  C 91 * X ^ 27 +
  C 26 * X ^ 28 +
  C 575 * X ^ 29 +
  C 419 * X ^ 30 +
  C 88 * X ^ 31 +
  C 114 * X ^ 32 +
  C 188 * X ^ 33 +
  C 135 * X ^ 34 +
  C 539 * X ^ 35 +
  C 490 * X ^ 36 +
  C 601 * X ^ 37 +
  C 508 * X ^ 38 +
  C 417 * X ^ 39 +
  C 291 * X ^ 40 +
  C 108 * X ^ 41 +
  C 425 * X ^ 42 +
  C 350 * X ^ 43 +
  C 318 * X ^ 44 +
  C 276 * X ^ 45 +
  C 362 * X ^ 46 +
  C 167 * X ^ 47 +
  C 58 * X ^ 48 +
  C 120 * X ^ 49 +
  C 607 * X ^ 50 +
  C 21 * X ^ 51 +
  C 377 * X ^ 52 +
  C 243 * X ^ 53 +
  C 48 * X ^ 54 +
  C 520 * X ^ 55 +
  C 176 * X ^ 56 +
  C 323 * X ^ 57 +
  C 100 * X ^ 58 +
  C 343 * X ^ 59 +
  C 32 * X ^ 60 +
  C 458 * X ^ 61 +
  C 165 * X ^ 62 +
  C 188 * X ^ 63 +
  C 141 * X ^ 64 +
  C 39 * X ^ 65 +
  C 474 * X ^ 66 +
  C 439 * X ^ 67 +
  C 437 * X ^ 68 +
  C 576 * X ^ 69 +
  C 487 * X ^ 70 +
  C 376 * X ^ 71 +
  C 485 * X ^ 72 +
  C 478 * X ^ 73 +
  C 13 * X ^ 74 +
  C 588 * X ^ 75 +
  C 595 * X ^ 76 +
  C 214 * X ^ 77 +
  C 425 * X ^ 78 +
  C 332 * X ^ 79 +
  C 185 * X ^ 80 +
  C 254 * X ^ 81 +
  C 591 * X ^ 82 +
  C 119 * X ^ 83 +
  C 367 * X ^ 84 +
  C 238 * X ^ 85 +
  C 229 * X ^ 86 +
  C 198 * X ^ 87 +
  C 366 * X ^ 88 +
  C 451 * X ^ 89 +
  C 517 * X ^ 90 +
  C 273 * X ^ 91 +
  C 465 * X ^ 92 +
  C 591 * X ^ 93 +
  C 539 * X ^ 94 +
  C 285 * X ^ 95 +
  C 91 * X ^ 96 +
  C 1 * X ^ 97 +
  C 507 * X ^ 98 +
  C 495 * X ^ 99 +
  C 599 * X ^ 100 +
  C 29 * X ^ 101 +
  C 223 * X ^ 102 +
  C 143 * X ^ 103 +
  C 416 * X ^ 104 +
  C 17 * X ^ 105 +
  C 45 * X ^ 106 +
  C 468 * X ^ 107 +
  C 393 * X ^ 108 +
  C 502 * X ^ 109

lemma natDegree_G_le : G.natDegree ≤ 12 := by unfold G; compute_degree!
lemma natDegree_T1_le : T1.natDegree ≤ 11 := by unfold T1; compute_degree!
lemma natDegree_T2_le : T2.natDegree ≤ 11 := by unfold T2; compute_degree!
lemma S1_natDegree_le : S1.natDegree ≤ 109 := by unfold S1; compute_degree!

theorem chain1_identity : G * S1 = (T1).comp T1 - T2 := by
  have hL : (G * S1).natDegree ≤ 121 := by
    calc (G * S1).natDegree ≤ G.natDegree + S1.natDegree := natDegree_mul_le
      _ ≤ 12 + 109 := by have h1 := natDegree_G_le; have h2 := S1_natDegree_le; omega
  have hR : ((T1).comp T1 - T2).natDegree ≤ 121 := by
    apply natDegree_sub_le_of_le (m := 121) (n := 121)
    · calc ((T1).comp T1).natDegree ≤ T1.natDegree * T1.natDegree := natDegree_comp_le
        _ ≤ 11 * 11 := by have h1 := natDegree_T1_le; have h2 := natDegree_T1_le; nlinarith
    · have h := natDegree_T2_le; omega
  refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq (G * S1) ((T1).comp T1 - T2)
    (f := pts) pts_injective ?_ ?_
  · intro i
    fin_cases i <;>
      (simp [G, S1, T1, T1, T2, pts, Polynomial.eval_comp]
       decide +revert)
  · simp only [Fintype.card_fin]
    omega

theorem chain_dvd_1 : G ∣ (T1).comp T1 - T2 := ⟨S1, chain1_identity.symm⟩

end LeanFormal.IUT.XiFPaper.S2566ChainComp1aActual
end