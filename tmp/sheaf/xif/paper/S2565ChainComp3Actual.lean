import tmp.sheaf.xif.paper.S2554Mod613ChainDataActual

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial

/-!
# Chain steps k = 9, 10, 11 for the mod-613 polynomial T

For k in {9,10,11} we exhibit the explicit quotient S_k of
(T_k).comp T1 - T_{k+1} by the monic polynomial G, of degree at most 109.
The identity G * S_k = (T_k).comp T1 - T_{k+1} is proved by checking
equality at the 122 points 0, ..., 121 of ZMod 613: both sides have
degree at most 121, and ZMod 613 is a domain, so a polynomial of degree
< 122 vanishing at 122 distinct points is zero.
-/

namespace LeanFormal.IUT.XiFPaper.S2565ChainComp3Actual

open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual

/-- Explicit quotient of (T9).comp T1 - T10 by G. -/
def S9 : (ZMod 613)[X] := C 317 + C 45 * X + C 22 * X ^ 2 + C 599 * X ^ 3 + C 166 * X ^ 4 + C 144 * X ^ 5 + C 5 * X ^ 6 + C 390 * X ^ 7 + C 282 * X ^ 8 + C 456 * X ^ 9 + C 395 * X ^ 10 + C 387 * X ^ 11 + C 516 * X ^ 12 + C 22 * X ^ 13 + C 152 * X ^ 14 + C 556 * X ^ 15 + C 385 * X ^ 16 + C 515 * X ^ 17 + C 236 * X ^ 18 + C 55 * X ^ 19 + C 295 * X ^ 20 + C 481 * X ^ 21 + C 491 * X ^ 22 + C 54 * X ^ 23 + C 503 * X ^ 24 + C 160 * X ^ 25 + C 105 * X ^ 26 + C 295 * X ^ 27 + C 166 * X ^ 28 + C 521 * X ^ 29 + C 500 * X ^ 30 + C 99 * X ^ 31 + C 223 * X ^ 32 + C 288 * X ^ 33 + C 125 * X ^ 34 + C 344 * X ^ 35 + C 418 * X ^ 36 + C 217 * X ^ 37 + C 233 * X ^ 38 + C 162 * X ^ 39 + C 358 * X ^ 40 + C 321 * X ^ 41 + C 59 * X ^ 42 + C 443 * X ^ 43 + C 435 * X ^ 44 + C 591 * X ^ 45 + C 548 * X ^ 46 + C 282 * X ^ 47 + C 593 * X ^ 48 + C 575 * X ^ 49 + C 492 * X ^ 50 + C 346 * X ^ 51 + C 447 * X ^ 52 + C 299 * X ^ 53 + C 170 * X ^ 54 + C 261 * X ^ 55 + C 591 * X ^ 56 + C 97 * X ^ 57 + C 462 * X ^ 58 + C 317 * X ^ 59 + C 237 * X ^ 60 + C 265 * X ^ 61 + C 508 * X ^ 62 + C 386 * X ^ 63 + C 421 * X ^ 64 + C 130 * X ^ 65 + C 252 * X ^ 66 + C 611 * X ^ 67 + C 471 * X ^ 68 + C 213 * X ^ 69 + C 344 * X ^ 70 + C 158 * X ^ 71 + C 284 * X ^ 72 + C 117 * X ^ 73 + C 408 * X ^ 74 + C 551 * X ^ 75 + C 15 * X ^ 76 + C 166 * X ^ 77 + C 245 * X ^ 78 + C 108 * X ^ 79 + C 605 * X ^ 80 + C 187 * X ^ 81 + C 388 * X ^ 82 + C 271 * X ^ 83 + C 399 * X ^ 84 + C 55 * X ^ 85 + C 356 * X ^ 86 + C 144 * X ^ 87 + C 174 * X ^ 88 + C 475 * X ^ 89 + C 464 * X ^ 90 + C 261 * X ^ 91 + C 466 * X ^ 92 + C 333 * X ^ 93 + C 581 * X ^ 94 + C 479 * X ^ 95 + C 420 * X ^ 96 + C 122 * X ^ 97 + C 307 * X ^ 98 + C 527 * X ^ 99 + C 395 * X ^ 100 + C 364 * X ^ 101 + C 495 * X ^ 102 + C 125 * X ^ 103 + C 85 * X ^ 104 + C 2 * X ^ 105 + C 438 * X ^ 106 + C 19 * X ^ 107 + C 515 * X ^ 108 + C 23 * X ^ 109

/-- Explicit quotient of (T10).comp T1 - T11 by G. -/
def S10 : (ZMod 613)[X] := C 188 + C 506 * X + C 493 * X ^ 2 + C 124 * X ^ 3 + C 389 * X ^ 4 + C 151 * X ^ 5 + C 467 * X ^ 6 + C 419 * X ^ 7 + C 362 * X ^ 8 + C 493 * X ^ 9 + C 265 * X ^ 10 + C 525 * X ^ 11 + C 61 * X ^ 12 + C 525 * X ^ 13 + C 36 * X ^ 14 + C 262 * X ^ 15 + C 243 * X ^ 16 + C 417 * X ^ 17 + C 233 * X ^ 18 + C 135 * X ^ 19 + C 368 * X ^ 20 + C 567 * X ^ 21 + C 58 * X ^ 22 + C 58 * X ^ 23 + C 12 * X ^ 24 + C 470 * X ^ 25 + C 354 * X ^ 26 + C 477 * X ^ 27 + C 453 * X ^ 28 + C 540 * X ^ 29 + C 506 * X ^ 30 + C 9 * X ^ 31 + C 239 * X ^ 32 + C 145 * X ^ 33 + C 151 * X ^ 34 + C 197 * X ^ 35 + C 599 * X ^ 36 + C 245 * X ^ 37 + C 25 * X ^ 38 + C 191 * X ^ 39 + C 111 * X ^ 40 + C 176 * X ^ 41 + C 377 * X ^ 42 + C 237 * X ^ 43 + C 334 * X ^ 44 + C 540 * X ^ 45 + C 521 * X ^ 46 + C 209 * X ^ 47 + C 505 * X ^ 48 + C 525 * X ^ 49 + C 434 * X ^ 50 + C 38 * X ^ 51 + C 454 * X ^ 52 + C 150 * X ^ 53 + C 332 * X ^ 54 + C 457 * X ^ 55 + C 466 * X ^ 56 + C 79 * X ^ 57 + C 472 * X ^ 58 + C 53 * X ^ 59 + C 408 * X ^ 60 + C 270 * X ^ 61 + C 429 * X ^ 62 + C 108 * X ^ 63 + C 520 * X ^ 64 + C 177 * X ^ 65 + C 452 * X ^ 66 + C 87 * X ^ 67 + C 493 * X ^ 68 + C 371 * X ^ 69 + C 177 * X ^ 70 + C 310 * X ^ 71 + C 410 * X ^ 72 + C 507 * X ^ 73 + C 528 * X ^ 74 + C 60 * X ^ 75 + C 113 * X ^ 76 + C 200 * X ^ 77 + C 428 * X ^ 78 + C 106 * X ^ 79 + C 603 * X ^ 80 + C 405 * X ^ 81 + C 235 * X ^ 82 + C 323 * X ^ 83 + C 488 * X ^ 84 + C 29 * X ^ 85 + C 514 * X ^ 86 + C 144 * X ^ 87 + C 377 * X ^ 88 + C 350 * X ^ 89 + C 338 * X ^ 90 + C 229 * X ^ 91 + C 142 * X ^ 92 + C 234 * X ^ 93 + C 319 * X ^ 94 + C 431 * X ^ 95 + C 215 * X ^ 96 + C 449 * X ^ 97 + C 354 * X ^ 98 + C 443 * X ^ 99 + C 11 * X ^ 100 + C 21 * X ^ 101 + C 394 * X ^ 102 + C 19 * X ^ 103 + C 111 * X ^ 104 + C 118 * X ^ 105 + C 96 * X ^ 106 + C 508 * X ^ 107 + C 348 * X ^ 108 + C 131 * X ^ 109

/-- Explicit quotient of (T11).comp T1 - T12 by G. -/
def S11 : (ZMod 613)[X] := C 8 + C 137 * X + C 198 * X ^ 2 + C 488 * X ^ 3 + C 528 * X ^ 4 + C 377 * X ^ 5 + C 86 * X ^ 6 + C 273 * X ^ 7 + C 9 * X ^ 8 + C 412 * X ^ 9 + C 9 * X ^ 10 + C 217 * X ^ 11 + C 280 * X ^ 12 + C 577 * X ^ 13 + C 408 * X ^ 14 + C 312 * X ^ 15 + C 417 * X ^ 16 + C 522 * X ^ 17 + C 201 * X ^ 18 + C 458 * X ^ 19 + C 172 * X ^ 20 + C 535 * X ^ 21 + C 251 * X ^ 22 + C 116 * X ^ 23 + C 250 * X ^ 24 + C 608 * X ^ 25 + C 424 * X ^ 26 + C 340 * X ^ 27 + C 114 * X ^ 28 + C 146 * X ^ 29 + C 502 * X ^ 30 + C 99 * X ^ 31 + C 427 * X ^ 32 + C 425 * X ^ 33 + C 79 * X ^ 34 + C 354 * X ^ 35 + C 65 * X ^ 36 + C 529 * X ^ 37 + C 89 * X ^ 38 + C 436 * X ^ 39 + C 379 * X ^ 40 + C 277 * X ^ 41 + C 187 * X ^ 42 + C 27 * X ^ 43 + C 415 * X ^ 44 + C 316 * X ^ 45 + C 284 * X ^ 46 + C 43 * X ^ 47 + C 115 * X ^ 48 + C 226 * X ^ 49 + C 261 * X ^ 50 + C 547 * X ^ 51 + C 282 * X ^ 52 + C 559 * X ^ 53 + C 514 * X ^ 54 + C 307 * X ^ 55 + C 106 * X ^ 56 + C 612 * X ^ 57 + C 456 * X ^ 58 + C 68 * X ^ 59 + C 518 * X ^ 60 + C 423 * X ^ 61 + C 293 * X ^ 62 + C 204 * X ^ 63 + C 581 * X ^ 64 + C 33 * X ^ 65 + C 173 * X ^ 66 + C 510 * X ^ 67 + C 536 * X ^ 68 + C 196 * X ^ 69 + C 36 * X ^ 70 + C 313 * X ^ 71 + C 504 * X ^ 72 + C 227 * X ^ 73 + C 247 * X ^ 74 + C 104 * X ^ 75 + C 403 * X ^ 76 + C 370 * X ^ 77 + C 600 * X ^ 78 + C 250 * X ^ 79 + C 376 * X ^ 80 + C 191 * X ^ 81 + C 112 * X ^ 82 + C 93 * X ^ 83 + C 417 * X ^ 84 + C 325 * X ^ 85 + C 594 * X ^ 86 + C 265 * X ^ 87 + C 40 * X ^ 88 + C 606 * X ^ 89 + C 488 * X ^ 90 + C 515 * X ^ 91 + C 153 * X ^ 92 + C 183 * X ^ 93 + C 577 * X ^ 94 + C 16 * X ^ 95 + C 234 * X ^ 96 + C 149 * X ^ 97 + C 496 * X ^ 98 + C 140 * X ^ 99 + C 27 * X ^ 100 + C 163 * X ^ 101 + C 577 * X ^ 102 + C 381 * X ^ 103 + C 161 * X ^ 104 + C 11 * X ^ 105 + C 570 * X ^ 106 + C 411 * X ^ 107 + C 74 * X ^ 108 + C 433 * X ^ 109

/-! ## The evaluation points 0, ..., 121 of ZMod 613. -/

lemma point_injection :
    Function.Injective (fun i : Fin 122 => ((i : ℕ) : ZMod 613)) := by
  intro i j h
  have hi : (i : ℕ) < 613 := by have := i.isLt; omega
  have hj : (j : ℕ) < 613 := by have := j.isLt; omega
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h
  exact Fin.ext h

/-! ## Degree bounds -/

lemma natDegree_G_le : G.natDegree ≤ 12 := by
  unfold G
  compute_degree!

lemma natDegree_T1_le : T1.natDegree ≤ 11 := by
  unfold T1
  compute_degree!

lemma natDegree_T9_le : T9.natDegree ≤ 11 := by
  unfold T9
  compute_degree!

lemma natDegree_T10_le : T10.natDegree ≤ 11 := by
  unfold T10
  compute_degree!

lemma natDegree_T11_le : T11.natDegree ≤ 11 := by
  unfold T11
  compute_degree!

lemma natDegree_T12_le : T12.natDegree ≤ 1 := by
  unfold T12
  compute_degree!

lemma natDegree_S9_le : S9.natDegree ≤ 109 := by
  unfold S9
  compute_degree!

lemma natDegree_S10_le : S10.natDegree ≤ 109 := by
  unfold S10
  compute_degree!

lemma natDegree_S11_le : S11.natDegree ≤ 109 := by
  unfold S11
  compute_degree!

lemma natDegree_G_mul_S9_le : (G * S9).natDegree ≤ 121 := by
  calc (G * S9).natDegree ≤ G.natDegree + S9.natDegree :=
        Polynomial.natDegree_mul_le
    _ ≤ 12 + 109 := Nat.add_le_add natDegree_G_le natDegree_S9_le
    _ = 121 := by norm_num

lemma natDegree_G_mul_S10_le : (G * S10).natDegree ≤ 121 := by
  calc (G * S10).natDegree ≤ G.natDegree + S10.natDegree :=
        Polynomial.natDegree_mul_le
    _ ≤ 12 + 109 := Nat.add_le_add natDegree_G_le natDegree_S10_le
    _ = 121 := by norm_num

lemma natDegree_G_mul_S11_le : (G * S11).natDegree ≤ 121 := by
  calc (G * S11).natDegree ≤ G.natDegree + S11.natDegree :=
        Polynomial.natDegree_mul_le
    _ ≤ 12 + 109 := Nat.add_le_add natDegree_G_le natDegree_S11_le
    _ = 121 := by norm_num

lemma natDegree_comp_T9_le : (T9.comp T1).natDegree ≤ 121 := by
  calc (T9.comp T1).natDegree ≤ T9.natDegree * T1.natDegree :=
        Polynomial.natDegree_comp_le
    _ ≤ 11 * 11 := Nat.mul_le_mul natDegree_T9_le natDegree_T1_le
    _ = 121 := by norm_num

lemma natDegree_R9_le : (T9.comp T1 - T10).natDegree ≤ 121 := by
  calc (T9.comp T1 - T10).natDegree ≤ max (T9.comp T1).natDegree T10.natDegree :=
        Polynomial.natDegree_sub_le _ _
    _ ≤ 121 := max_le natDegree_comp_T9_le (by have := natDegree_T10_le; omega)

lemma natDegree_comp_T10_le : (T10.comp T1).natDegree ≤ 121 := by
  calc (T10.comp T1).natDegree ≤ T10.natDegree * T1.natDegree :=
        Polynomial.natDegree_comp_le
    _ ≤ 11 * 11 := Nat.mul_le_mul natDegree_T10_le natDegree_T1_le
    _ = 121 := by norm_num

lemma natDegree_R10_le : (T10.comp T1 - T11).natDegree ≤ 121 := by
  calc (T10.comp T1 - T11).natDegree ≤ max (T10.comp T1).natDegree T11.natDegree :=
        Polynomial.natDegree_sub_le _ _
    _ ≤ 121 := max_le natDegree_comp_T10_le (by have := natDegree_T11_le; omega)

lemma natDegree_comp_T11_le : (T11.comp T1).natDegree ≤ 121 := by
  calc (T11.comp T1).natDegree ≤ T11.natDegree * T1.natDegree :=
        Polynomial.natDegree_comp_le
    _ ≤ 11 * 11 := Nat.mul_le_mul natDegree_T11_le natDegree_T1_le
    _ = 121 := by norm_num

lemma natDegree_R11_le : (T11.comp T1 - T12).natDegree ≤ 121 := by
  calc (T11.comp T1 - T12).natDegree ≤ max (T11.comp T1).natDegree T12.natDegree :=
        Polynomial.natDegree_sub_le _ _
    _ ≤ 121 := max_le natDegree_comp_T11_le (by have := natDegree_T12_le; omega)

/-- S9 really is the quotient of (T9).comp T1 - T10 by G. -/
theorem identity_9 : G * S9 = T9.comp T1 - T10 := by
  haveI : Fact (Nat.Prime 613) := ⟨by norm_num⟩
  refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq (G * S9) (T9.comp T1 - T10)
    (f := fun i : Fin 122 => ((i : ℕ) : ZMod 613)) point_injection ?_ ?_
  · intro i
    fin_cases i <;>
      (simp [G, S9, T9, T10, T1,
        Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_comp] <;>
        decide +revert)
  · simp only [Fintype.card_fin]
    have h1 := natDegree_G_mul_S9_le
    have h2 := natDegree_R9_le
    omega

/-- S10 really is the quotient of (T10).comp T1 - T11 by G. -/
theorem identity_10 : G * S10 = T10.comp T1 - T11 := by
  haveI : Fact (Nat.Prime 613) := ⟨by norm_num⟩
  refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq (G * S10) (T10.comp T1 - T11)
    (f := fun i : Fin 122 => ((i : ℕ) : ZMod 613)) point_injection ?_ ?_
  · intro i
    fin_cases i <;>
      (simp [G, S10, T10, T11, T1,
        Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_comp] <;>
        decide +revert)
  · simp only [Fintype.card_fin]
    have h1 := natDegree_G_mul_S10_le
    have h2 := natDegree_R10_le
    omega

/-- S11 really is the quotient of (T11).comp T1 - T12 by G. -/
theorem identity_11 : G * S11 = T11.comp T1 - T12 := by
  haveI : Fact (Nat.Prime 613) := ⟨by norm_num⟩
  refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq (G * S11) (T11.comp T1 - T12)
    (f := fun i : Fin 122 => ((i : ℕ) : ZMod 613)) point_injection ?_ ?_
  · intro i
    fin_cases i <;>
      (simp [G, S11, T11, T12, T1,
        Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_comp] <;>
        decide +revert)
  · simp only [Fintype.card_fin]
    have h1 := natDegree_G_mul_S11_le
    have h2 := natDegree_R11_le
    omega

/-- G divides (T9).comp T1 - T10. -/
theorem chain_dvd_9 : G ∣ T9.comp T1 - T10 := ⟨S9, identity_9.symm⟩

/-- G divides (T10).comp T1 - T11. -/
theorem chain_dvd_10 : G ∣ T10.comp T1 - T11 := ⟨S10, identity_10.symm⟩

/-- G divides (T11).comp T1 - T12. -/
theorem chain_dvd_11 : G ∣ T11.comp T1 - T12 := ⟨S11, identity_11.symm⟩

end LeanFormal.IUT.XiFPaper.S2565ChainComp3Actual

end

