/- S2566: composition chain steps k = 1,2,3,4 for G over ZMod 613. -/
import tmp.sheaf.xif.paper.S2554Mod613ChainDataActual
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Field.ZMod

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2566ChainComp1Actual

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
lemma natDegree_T2_le : T2.natDegree ≤ 11 := by unfold T2; compute_degree!
lemma natDegree_T3_le : T3.natDegree ≤ 11 := by unfold T3; compute_degree!
lemma natDegree_T4_le : T4.natDegree ≤ 11 := by unfold T4; compute_degree!
lemma natDegree_T5_le : T5.natDegree ≤ 11 := by unfold T5; compute_degree!
lemma natDegree_T6_le : T6.natDegree ≤ 11 := by unfold T6; compute_degree!
lemma S1_natDegree_le : S1.natDegree ≤ 109 := by unfold S1; compute_degree!
lemma S2_natDegree_le : S2.natDegree ≤ 109 := by unfold S2; compute_degree!
lemma S3_natDegree_le : S3.natDegree ≤ 109 := by unfold S3; compute_degree!
lemma S4_natDegree_le : S4.natDegree ≤ 109 := by unfold S4; compute_degree!

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

end LeanFormal.IUT.XiFPaper.S2566ChainComp1Actual
end