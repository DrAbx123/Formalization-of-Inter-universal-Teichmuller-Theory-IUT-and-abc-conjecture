/-
S2565: second half of the composition chain for the degree-12 polynomial G.

For k = 5, 6, 7, 8 we prove
  G divides (T_k).comp T1 - T_{k+1}
by exhibiting the explicit quotient S_k of degree 109, obtained by dividing
(T_k).comp T1 - T_{k+1} by G over GF(613).

The polynomial identity  G * S_k = (T_k).comp T1 - T_{k+1}  is checked by
evaluation at the 122 points 0,...,121 of ZMod 613.  Both sides have
natDegree at most 121 < 122 and ZMod 613 is a field, so evaluation at
these points forces polynomial equality
(Polynomial.eq_of_natDegree_lt_card_of_eval_eq).
Every point evaluation is a closed computation in ZMod 613 closed by decide.

No axioms, no sorry, no native_decide.
-/

import tmp.sheaf.xif.paper.S2554Mod613ChainDataActual
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Field.ZMod

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2565ChainComp2Actual

open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual

instance : Fact (Nat.Prime 613) := ⟨by norm_num⟩

/-! ### The evaluation points 0, ..., 121 -/

/-- The 122 evaluation points used to pin down polynomials of degree at most 121. -/
def pts (i : Fin 122) : ZMod 613 := ((i : ℕ) : ZMod 613)

lemma pts_injective : Function.Injective pts := by
  intro a b h
  have hv : ((a : ℕ) : ZMod 613).val = ((b : ℕ) : ZMod 613).val := by
    simpa only [pts] using congrArg ZMod.val h
  rw [ZMod.val_natCast, ZMod.val_natCast] at hv
  rw [Nat.mod_eq_of_lt (by have := a.isLt; omega),
    Nat.mod_eq_of_lt (by have := b.isLt; omega)] at hv
  exact Fin.ext hv

/-! ### The explicit quotients -/

/-- The quotient of (T5).comp T1 - T6 by G over ZMod 613. -/
def S5 : (ZMod 613)[X] :=
  C 290 + C 537 * X + C 284 * X ^ 2 + C 384 * X ^ 3 + C 439 * X ^ 4 + C 84 * X ^ 5 + C 424 * X ^ 6 + C 100 * X ^ 7 + C 498 * X ^ 8 + C 224 * X ^ 9 + C 515 * X ^ 10 + C 289 * X ^ 11 + C 483 * X ^ 12 + C 358 * X ^ 13 + C 182 * X ^ 14 + C 178 * X ^ 15 + C 45 * X ^ 16 + C 452 * X ^ 17 + C 571 * X ^ 18 + C 156 * X ^ 19 + C 490 * X ^ 20 + C 157 * X ^ 21 + C 551 * X ^ 22 + C 496 * X ^ 23 + C 121 * X ^ 24 + C 543 * X ^ 25 + C 555 * X ^ 26 + C 588 * X ^ 27 + C 530 * X ^ 28 + C 363 * X ^ 29 + C 612 * X ^ 30 + C 598 * X ^ 31 + C 286 * X ^ 32 + C 411 * X ^ 33 + C 321 * X ^ 34 + C 117 * X ^ 35 + C 14 * X ^ 36 + C 359 * X ^ 37 + C 461 * X ^ 38 + C 21 * X ^ 39 + C 219 * X ^ 40 + C 405 * X ^ 41 + C 591 * X ^ 42 + C 402 * X ^ 43 + C 359 * X ^ 44 + C 241 * X ^ 45 + C 528 * X ^ 46 + C 394 * X ^ 47 + C 54 * X ^ 48 + C 484 * X ^ 49 + C 238 * X ^ 50 + C 126 * X ^ 51 + C 519 * X ^ 52 + C 216 * X ^ 53 + C 330 * X ^ 54 + C 110 * X ^ 55 + C 408 * X ^ 56 + C 240 * X ^ 57 + C 182 * X ^ 58 + C 92 * X ^ 59 + C 104 * X ^ 60 + C 192 * X ^ 61 + C 133 * X ^ 62 + C 521 * X ^ 63 + C 97 * X ^ 64 + C 94 * X ^ 65 + C 349 * X ^ 66 + C 237 * X ^ 67 + C 238 * X ^ 68 + C 209 * X ^ 69 + C 193 * X ^ 70 + C 28 * X ^ 71 + C 331 * X ^ 72 + C 243 * X ^ 73 + C 230 * X ^ 74 + C 403 * X ^ 75 + C 176 * X ^ 76 + C 556 * X ^ 77 + C 191 * X ^ 78 + C 579 * X ^ 79 + C 535 * X ^ 80 + C 115 * X ^ 81 + C 17 * X ^ 82 + C 461 * X ^ 83 + C 528 * X ^ 84 + C 361 * X ^ 85 + C 569 * X ^ 86 + C 144 * X ^ 87 + C 587 * X ^ 88 + C 69 * X ^ 89 + C 171 * X ^ 90 + C 199 * X ^ 91 + C 573 * X ^ 92 + C 256 * X ^ 93 + C 346 * X ^ 94 + C 349 * X ^ 95 + C 561 * X ^ 96 + C 282 * X ^ 97 + C 234 * X ^ 98 + C 291 * X ^ 99 + C 367 * X ^ 100 + C 422 * X ^ 101 + C 328 * X ^ 102 + C 411 * X ^ 103 + C 304 * X ^ 104 + C 36 * X ^ 105 + C 528 * X ^ 106 + C 342 * X ^ 107 + C 75 * X ^ 108 + C 414 * X ^ 109

/-- The quotient of (T6).comp T1 - T7 by G over ZMod 613. -/
def S6 : (ZMod 613)[X] :=
  C 433 + C 286 * X + C 571 * X ^ 2 + C 368 * X ^ 3 + C 327 * X ^ 4 + C 92 * X ^ 5 + C 207 * X ^ 6 + C 40 * X ^ 7 + C 409 * X ^ 8 + C 566 * X ^ 9 + C 595 * X ^ 10 + C 202 * X ^ 11 + C 387 * X ^ 12 + C 129 * X ^ 13 + C 556 * X ^ 14 + C 127 * X ^ 15 + C 608 * X ^ 16 + C 274 * X ^ 17 + C 463 * X ^ 18 + C 461 * X ^ 19 + C 606 * X ^ 20 + C 592 * X ^ 21 + C 586 * X ^ 22 + C 460 * X ^ 23 + C 128 * X ^ 24 + C 458 * X ^ 25 + C 547 * X ^ 26 + C 292 * X ^ 27 + C 481 * X ^ 28 + C 412 * X ^ 29 + C 450 * X ^ 30 + C 289 * X ^ 31 + C 269 * X ^ 32 + C 499 * X ^ 33 + C 508 * X ^ 34 + C 472 * X ^ 35 + C 100 * X ^ 36 + C 221 * X ^ 37 + C 530 * X ^ 38 + C 97 * X ^ 39 + C 45 * X ^ 40 + C 155 * X ^ 41 + C 147 * X ^ 42 + C 168 * X ^ 43 + C 170 * X ^ 44 + C 143 * X ^ 45 + C 424 * X ^ 46 + C 127 * X ^ 47 + C 51 * X ^ 48 + C 427 * X ^ 49 + C 302 * X ^ 50 + C 53 * X ^ 51 + C 237 * X ^ 52 + C 1 * X ^ 53 + C 417 * X ^ 54 + C 185 * X ^ 55 + C 32 * X ^ 56 + C 204 * X ^ 57 + C 440 * X ^ 58 + C 106 * X ^ 59 + C 574 * X ^ 60 + C 596 * X ^ 61 + C 465 * X ^ 62 + C 237 * X ^ 63 + C 366 * X ^ 64 + C 55 * X ^ 65 + C 202 * X ^ 66 + C 183 * X ^ 67 + C 22 * X ^ 68 + C 340 * X ^ 69 + C 443 * X ^ 70 + C 309 * X ^ 71 + C 81 * X ^ 72 + C 236 * X ^ 73 + C 441 * X ^ 74 + C 521 * X ^ 75 + C 200 * X ^ 76 + C 194 * X ^ 77 + C 142 * X ^ 78 + C 476 * X ^ 79 + C 480 * X ^ 80 + C 287 * X ^ 81 + C 148 * X ^ 82 + C 461 * X ^ 83 + C 474 * X ^ 84 + C 559 * X ^ 85 + C 90 * X ^ 86 + C 25 * X ^ 87 + C 149 * X ^ 88 + C 205 * X ^ 89 + C 229 * X ^ 90 + C 155 * X ^ 91 + C 478 * X ^ 92 + C 221 * X ^ 93 + C 342 * X ^ 94 + C 179 * X ^ 95 + C 307 * X ^ 96 + C 144 * X ^ 97 + C 349 * X ^ 98 + C 127 * X ^ 99 + C 493 * X ^ 100 + C 161 * X ^ 101 + C 160 * X ^ 102 + C 350 * X ^ 103 + C 238 * X ^ 104 + C 496 * X ^ 105 + C 123 * X ^ 106 + C 421 * X ^ 107 + C 216 * X ^ 108 + C 187 * X ^ 109

/-- The quotient of (T7).comp T1 - T8 by G over ZMod 613. -/
def S7 : (ZMod 613)[X] :=
  C 430 + C 101 * X + C 6 * X ^ 2 + C 155 * X ^ 3 + C 561 * X ^ 4 + C 169 * X ^ 5 + C 554 * X ^ 6 + C 134 * X ^ 7 + C 282 * X ^ 8 + C 260 * X ^ 9 + C 184 * X ^ 10 + C 313 * X ^ 11 + C 426 * X ^ 12 + C 452 * X ^ 13 + C 592 * X ^ 14 + C 554 * X ^ 15 + C 600 * X ^ 16 + C 571 * X ^ 17 + C 331 * X ^ 18 + C 322 * X ^ 19 + C 208 * X ^ 20 + C 215 * X ^ 21 + C 277 * X ^ 22 + C 36 * X ^ 23 + C 160 * X ^ 24 + C 323 * X ^ 25 + C 73 * X ^ 26 + C 241 * X ^ 27 + C 208 * X ^ 28 + C 140 * X ^ 29 + C 256 * X ^ 30 + C 541 * X ^ 31 + C 412 * X ^ 32 + C 543 * X ^ 33 + C 58 * X ^ 34 + C 324 * X ^ 35 + C 432 * X ^ 36 + C 449 * X ^ 37 + C 379 * X ^ 38 + C 607 * X ^ 39 + C 574 * X ^ 40 + C 564 * X ^ 41 + C 230 * X ^ 42 + C 184 * X ^ 43 + C 512 * X ^ 44 + C 472 * X ^ 45 + C 536 * X ^ 46 + C 60 * X ^ 47 + C 33 * X ^ 48 + C 414 * X ^ 49 + C 274 * X ^ 50 + C 362 * X ^ 51 + C 609 * X ^ 52 + C 302 * X ^ 53 + C 369 * X ^ 54 + C 607 * X ^ 55 + C 465 * X ^ 56 + C 588 * X ^ 57 + C 108 * X ^ 58 + C 444 * X ^ 59 + C 59 * X ^ 60 + C 552 * X ^ 61 + C 317 * X ^ 62 + C 511 * X ^ 63 + C 149 * X ^ 64 + C 294 * X ^ 65 + C 365 * X ^ 66 + C 250 * X ^ 67 + C 363 * X ^ 68 + C 369 * X ^ 69 + C 7 * X ^ 70 + C 352 * X ^ 71 + C 463 * X ^ 72 + C 444 * X ^ 73 + C 160 * X ^ 74 + C 226 * X ^ 75 + C 215 * X ^ 76 + C 162 * X ^ 77 + C 289 * X ^ 78 + C 124 * X ^ 79 + C 109 * X ^ 80 + C 609 * X ^ 81 + C 223 * X ^ 82 + C 482 * X ^ 83 + C 318 * X ^ 84 + C 604 * X ^ 85 + C 231 * X ^ 86 + C 539 * X ^ 87 + C 596 * X ^ 88 + C 500 * X ^ 89 + C 400 * X ^ 90 + C 478 * X ^ 91 + C 475 * X ^ 92 + C 109 * X ^ 93 + C 73 * X ^ 94 + C 139 * X ^ 95 + C 186 * X ^ 96 + C 47 * X ^ 97 + C 325 * X ^ 98 + C 272 * X ^ 99 + C 105 * X ^ 100 + C 89 * X ^ 101 + C 473 * X ^ 102 + C 460 * X ^ 103 + C 558 * X ^ 104 + C 179 * X ^ 105 + C 582 * X ^ 106 + C 168 * X ^ 107 + C 424 * X ^ 108 + C 526 * X ^ 109

/-- The quotient of (T8).comp T1 - T9 by G over ZMod 613. -/
def S8 : (ZMod 613)[X] :=
  C 473 + C 14 * X + C 332 * X ^ 2 + C 381 * X ^ 3 + C 592 * X ^ 4 + C 83 * X ^ 5 + C 65 * X ^ 6 + C 308 * X ^ 7 + C 289 * X ^ 8 + C 601 * X ^ 9 + C 47 * X ^ 10 + C 157 * X ^ 11 + C 387 * X ^ 12 + C 447 * X ^ 13 + C 512 * X ^ 14 + C 99 * X ^ 15 + C 219 * X ^ 16 + C 241 * X ^ 17 + C 42 * X ^ 18 + C 361 * X ^ 19 + C 597 * X ^ 20 + C 565 * X ^ 21 + C 190 * X ^ 22 + C 323 * X ^ 23 + C 135 * X ^ 24 + C 481 * X ^ 25 + C 221 * X ^ 26 + C 380 * X ^ 27 + C 251 * X ^ 28 + C 58 * X ^ 29 + C 512 * X ^ 30 + C 487 * X ^ 31 + C 251 * X ^ 32 + C 284 * X ^ 33 + C 264 * X ^ 34 + C 308 * X ^ 35 + C 95 * X ^ 36 + C 154 * X ^ 37 + C 230 * X ^ 38 + C 328 * X ^ 39 + C 68 * X ^ 40 + C 234 * X ^ 41 + C 558 * X ^ 42 + C 89 * X ^ 43 + C 537 * X ^ 44 + C 237 * X ^ 45 + C 116 * X ^ 46 + C 541 * X ^ 47 + C 492 * X ^ 48 + C 43 * X ^ 49 + C 343 * X ^ 50 + C 88 * X ^ 51 + C 525 * X ^ 52 + C 269 * X ^ 53 + C 468 * X ^ 54 + C 587 * X ^ 55 + C 338 * X ^ 56 + C 378 * X ^ 57 + C 612 * X ^ 58 + C 517 * X ^ 59 + C 386 * X ^ 60 + C 407 * X ^ 61 + C 367 * X ^ 62 + C 325 * X ^ 63 + C 496 * X ^ 64 + C 376 * X ^ 65 + C 586 * X ^ 66 + C 178 * X ^ 67 + C 479 * X ^ 68 + C 534 * X ^ 69 + C 426 * X ^ 70 + C 213 * X ^ 71 + C 122 * X ^ 72 + C 158 * X ^ 73 + C 103 * X ^ 74 + C 456 * X ^ 75 + C 500 * X ^ 76 + C 596 * X ^ 77 + C 172 * X ^ 78 + C 280 * X ^ 79 + C 178 * X ^ 80 + C 416 * X ^ 81 + C 449 * X ^ 82 + C 431 * X ^ 83 + C 498 * X ^ 84 + C 363 * X ^ 85 + C 282 * X ^ 86 + C 585 * X ^ 87 + C 566 * X ^ 88 + C 519 * X ^ 89 + C 219 * X ^ 90 + C 208 * X ^ 91 + C 70 * X ^ 92 + C 290 * X ^ 93 + C 499 * X ^ 95 + C 175 * X ^ 96 + C 37 * X ^ 97 + C 533 * X ^ 98 + C 589 * X ^ 99 + C 153 * X ^ 100 + C 515 * X ^ 101 + C 409 * X ^ 102 + C 320 * X ^ 103 + C 95 * X ^ 104 + C 471 * X ^ 105 + C 165 * X ^ 106 + C 490 * X ^ 107 + C 215 * X ^ 108 + C 206 * X ^ 109

/-! ### Degree bounds -/

lemma natDegree_G_le : G.natDegree ≤ 12 := by unfold G; compute_degree!

lemma natDegree_T1_le : T1.natDegree ≤ 11 := by unfold T1; compute_degree!

lemma natDegree_T5_le : T5.natDegree ≤ 11 := by unfold T5; compute_degree!

lemma natDegree_T6_le : T6.natDegree ≤ 11 := by unfold T6; compute_degree!

lemma natDegree_T7_le : T7.natDegree ≤ 11 := by unfold T7; compute_degree!

lemma natDegree_T8_le : T8.natDegree ≤ 11 := by unfold T8; compute_degree!

lemma natDegree_T9_le : T9.natDegree ≤ 11 := by unfold T9; compute_degree!

lemma S5_natDegree_le : S5.natDegree ≤ 109 := by unfold S5; compute_degree!

lemma S6_natDegree_le : S6.natDegree ≤ 109 := by unfold S6; compute_degree!

lemma S7_natDegree_le : S7.natDegree ≤ 109 := by unfold S7; compute_degree!

lemma S8_natDegree_le : S8.natDegree ≤ 109 := by unfold S8; compute_degree!

/-! ### The identities and the divisibility -/

theorem chain5_identity : G * S5 = (T5).comp T1 - T6 := by
  have hL : (G * S5).natDegree ≤ 121 := by
    calc (G * S5).natDegree ≤ G.natDegree + S5.natDegree := natDegree_mul_le
      _ ≤ 12 + 109 := by have h1 := natDegree_G_le; have h2 := S5_natDegree_le; omega
  have hR : ((T5).comp T1 - T6).natDegree ≤ 121 := by
    apply natDegree_sub_le_of_le (m := 121) (n := 121)
    · calc ((T5).comp T1).natDegree ≤ T5.natDegree * T1.natDegree := natDegree_comp_le
        _ ≤ 11 * 11 := by have h1 := natDegree_T5_le; have h2 := natDegree_T1_le; nlinarith
    · have h := natDegree_T6_le; omega
  refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq (G * S5) ((T5).comp T1 - T6)
    (f := pts) pts_injective ?_ ?_
  · intro i
    fin_cases i <;>
      (simp [G, S5, T5, T1, T6, pts, Polynomial.eval_comp]
       decide +revert)
  · simp only [Fintype.card_fin]
    omega

theorem chain_dvd_5 : G ∣ (T5).comp T1 - T6 := ⟨S5, chain5_identity.symm⟩

theorem chain6_identity : G * S6 = (T6).comp T1 - T7 := by
  have hL : (G * S6).natDegree ≤ 121 := by
    calc (G * S6).natDegree ≤ G.natDegree + S6.natDegree := natDegree_mul_le
      _ ≤ 12 + 109 := by have h1 := natDegree_G_le; have h2 := S6_natDegree_le; omega
  have hR : ((T6).comp T1 - T7).natDegree ≤ 121 := by
    apply natDegree_sub_le_of_le (m := 121) (n := 121)
    · calc ((T6).comp T1).natDegree ≤ T6.natDegree * T1.natDegree := natDegree_comp_le
        _ ≤ 11 * 11 := by have h1 := natDegree_T6_le; have h2 := natDegree_T1_le; nlinarith
    · have h := natDegree_T7_le; omega
  refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq (G * S6) ((T6).comp T1 - T7)
    (f := pts) pts_injective ?_ ?_
  · intro i
    fin_cases i <;>
      (simp [G, S6, T6, T1, T7, pts, Polynomial.eval_comp]
       decide +revert)
  · simp only [Fintype.card_fin]
    omega

theorem chain_dvd_6 : G ∣ (T6).comp T1 - T7 := ⟨S6, chain6_identity.symm⟩

theorem chain7_identity : G * S7 = (T7).comp T1 - T8 := by
  have hL : (G * S7).natDegree ≤ 121 := by
    calc (G * S7).natDegree ≤ G.natDegree + S7.natDegree := natDegree_mul_le
      _ ≤ 12 + 109 := by have h1 := natDegree_G_le; have h2 := S7_natDegree_le; omega
  have hR : ((T7).comp T1 - T8).natDegree ≤ 121 := by
    apply natDegree_sub_le_of_le (m := 121) (n := 121)
    · calc ((T7).comp T1).natDegree ≤ T7.natDegree * T1.natDegree := natDegree_comp_le
        _ ≤ 11 * 11 := by have h1 := natDegree_T7_le; have h2 := natDegree_T1_le; nlinarith
    · have h := natDegree_T8_le; omega
  refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq (G * S7) ((T7).comp T1 - T8)
    (f := pts) pts_injective ?_ ?_
  · intro i
    fin_cases i <;>
      (simp [G, S7, T7, T1, T8, pts, Polynomial.eval_comp]
       decide +revert)
  · simp only [Fintype.card_fin]
    omega

theorem chain_dvd_7 : G ∣ (T7).comp T1 - T8 := ⟨S7, chain7_identity.symm⟩

theorem chain8_identity : G * S8 = (T8).comp T1 - T9 := by
  have hL : (G * S8).natDegree ≤ 121 := by
    calc (G * S8).natDegree ≤ G.natDegree + S8.natDegree := natDegree_mul_le
      _ ≤ 12 + 109 := by have h1 := natDegree_G_le; have h2 := S8_natDegree_le; omega
  have hR : ((T8).comp T1 - T9).natDegree ≤ 121 := by
    apply natDegree_sub_le_of_le (m := 121) (n := 121)
    · calc ((T8).comp T1).natDegree ≤ T8.natDegree * T1.natDegree := natDegree_comp_le
        _ ≤ 11 * 11 := by have h1 := natDegree_T8_le; have h2 := natDegree_T1_le; nlinarith
    · have h := natDegree_T9_le; omega
  refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq (G * S8) ((T8).comp T1 - T9)
    (f := pts) pts_injective ?_ ?_
  · intro i
    fin_cases i <;>
      (simp [G, S8, T8, T1, T9, pts, Polynomial.eval_comp]
       decide +revert)
  · simp only [Fintype.card_fin]
    omega

theorem chain_dvd_8 : G ∣ (T8).comp T1 - T9 := ⟨S8, chain8_identity.symm⟩
end LeanFormal.IUT.XiFPaper.S2565ChainComp2Actual

end
