import tmp.sheaf.xif.paper.S2554Mod613ChainDataActual
import tmp.sheaf.xif.paper.S2560S0ShiftedPartsActual
import tmp.sheaf.xif.paper.S2562GmulCoeffActual
import tmp.sheaf.xif.paper.S2563R5LookupActual
import tmp.sheaf.xif.paper.S2563R6LookupActual

/-!
# Chain1, mid-range block 7: coefficients for n in [481, 560], X^613 - T1 versus G * S0

Target (one statement per n in [481, 560]):

  ((X : (ZMod 613)[X]) ^ 613 - T1).coeff n  =  (G * S0).coeff n

Since n < 613, the X^613 coefficient vanishes, so the left side is -T1.coeff n = 0
(as 12 <= n), and the right side is the 13-term support sum
  sum over a in range 13 of  G.coeff a * S0.coeff (n - a)     (G_mul_coeff_ge).

The needed S0.coeff k values (469 <= k <= 560) are read off the two active blocks of the
8-segment decomposition S0 = S0_0 + ... + S0_7:
* k = 401 + i  (68 <= i <= 79): only S0_5 = X^401 * R5 contributes, value R5.coeff i;
* k = 481 + j  (0 <= j <= 79):  only S0_6 = X^481 * R6 contributes, value R6.coeff j.
All other segments vanish at these indices (coefficient above the segment degree, or below the
segment shift). This is the content of S0_coeff_block5 / S0_coeff_block6.
-/

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2564Chain1Mid7Actual

open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual
open LeanFormal.IUT.XiFPaper.S2562GmulCoeffActual
open LeanFormal.IUT.XiFPaper.S2563R5LookupActual
open LeanFormal.IUT.XiFPaper.S2563R6LookupActual

/-! ## Degree bounds for the blocks R0 ... R5 and vanishing of the inactive S0 segments -/

lemma R0_deg : S2560S0ShiftedPartsActual.R0.natDegree ≤ 80 := by
  unfold S2560S0ShiftedPartsActual.R0; compute_degree!
lemma R1_deg : S2560S0ShiftedPartsActual.R1.natDegree ≤ 79 := by
  unfold S2560S0ShiftedPartsActual.R1; compute_degree!
lemma R2_deg : S2560S0ShiftedPartsActual.R2.natDegree ≤ 79 := by
  unfold S2560S0ShiftedPartsActual.R2; compute_degree!
lemma R3_deg : S2560S0ShiftedPartsActual.R3.natDegree ≤ 79 := by
  unfold S2560S0ShiftedPartsActual.R3; compute_degree!
lemma R4_deg : S2560S0ShiftedPartsActual.R4.natDegree ≤ 79 := by
  unfold S2560S0ShiftedPartsActual.R4; compute_degree!
lemma R5_deg : S2560S0ShiftedPartsActual.R5.natDegree ≤ 79 := by
  unfold S2560S0ShiftedPartsActual.R5; compute_degree!

lemma R0_coeff_zero (k : ℕ) (hk : 80 < k) : S2560S0ShiftedPartsActual.R0.coeff k = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have h := R0_deg; omega
lemma R1_coeff_zero (k : ℕ) (hk : 79 < k) : S2560S0ShiftedPartsActual.R1.coeff k = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have h := R1_deg; omega
lemma R2_coeff_zero (k : ℕ) (hk : 79 < k) : S2560S0ShiftedPartsActual.R2.coeff k = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have h := R2_deg; omega
lemma R3_coeff_zero (k : ℕ) (hk : 79 < k) : S2560S0ShiftedPartsActual.R3.coeff k = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have h := R3_deg; omega
lemma R4_coeff_zero (k : ℕ) (hk : 79 < k) : S2560S0ShiftedPartsActual.R4.coeff k = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have h := R4_deg; omega
lemma R5_coeff_zero (k : ℕ) (hk : 79 < k) : S2560S0ShiftedPartsActual.R5.coeff k = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have h := R5_deg; omega

lemma S0_0_coeff_zero (k : ℕ) (hk : 80 < k) : S0_0.coeff k = 0 := by
  rw [S0_0_coeff, if_pos (Nat.zero_le k), Nat.sub_zero]
  exact R0_coeff_zero k hk
lemma S0_1_coeff_zero (k : ℕ) (hk : 160 < k) : S0_1.coeff k = 0 := by
  rw [S0_1_coeff, if_pos (by omega)]
  exact R1_coeff_zero (k - 81) (by omega)
lemma S0_2_coeff_zero (k : ℕ) (hk : 240 < k) : S0_2.coeff k = 0 := by
  rw [S0_2_coeff, if_pos (by omega)]
  exact R2_coeff_zero (k - 161) (by omega)
lemma S0_3_coeff_zero (k : ℕ) (hk : 320 < k) : S0_3.coeff k = 0 := by
  rw [S0_3_coeff, if_pos (by omega)]
  exact R3_coeff_zero (k - 241) (by omega)
lemma S0_4_coeff_zero (k : ℕ) (hk : 400 < k) : S0_4.coeff k = 0 := by
  rw [S0_4_coeff, if_pos (by omega)]
  exact R4_coeff_zero (k - 321) (by omega)
lemma S0_5_coeff_zero (k : ℕ) (hk : 480 < k) : S0_5.coeff k = 0 := by
  rw [S0_5_coeff, if_pos (by omega)]
  exact R5_coeff_zero (k - 401) (by omega)
/-- S0_7 = X^561 * R7 has support starting at 561, so it vanishes below the shift. -/
lemma S0_7_coeff_eq_zero_of_lt (k : ℕ) (hk : k < 561) : S0_7.coeff k = 0 := by
  rw [S0_7_coeff, if_neg (by omega)]

/-! ## The two active blocks of S0 in the mid range -/

lemma S0_coeff_block6 (j : ℕ) (hj : j ≤ 79) :
    S0.coeff (481 + j) = S2560S0ShiftedPartsActual.R6.coeff j := by
  have h0 : S0_0.coeff (481 + j) = 0 := S0_0_coeff_zero (481 + j) (by omega)
  have h1 : S0_1.coeff (481 + j) = 0 := S0_1_coeff_zero (481 + j) (by omega)
  have h2 : S0_2.coeff (481 + j) = 0 := S0_2_coeff_zero (481 + j) (by omega)
  have h3 : S0_3.coeff (481 + j) = 0 := S0_3_coeff_zero (481 + j) (by omega)
  have h4 : S0_4.coeff (481 + j) = 0 := S0_4_coeff_zero (481 + j) (by omega)
  have h5 : S0_5.coeff (481 + j) = 0 := S0_5_coeff_zero (481 + j) (by omega)
  have h6 : S0_6.coeff (481 + j) = S2560S0ShiftedPartsActual.R6.coeff j := by
    rw [S0_6_coeff, if_pos (by omega), show 481 + j - 481 = j from by omega]
  have h7 : S0_7.coeff (481 + j) = 0 := S0_7_coeff_eq_zero_of_lt (481 + j) (by omega)
  simp only [S0, coeff_add, h0, h1, h2, h3, h4, h5, h6, h7, zero_add, add_zero]

lemma S0_coeff_block5 (i : ℕ) (hi : i ≤ 79) :
    S0.coeff (401 + i) = S2560S0ShiftedPartsActual.R5.coeff i := by
  have h0 : S0_0.coeff (401 + i) = 0 := S0_0_coeff_zero (401 + i) (by omega)
  have h1 : S0_1.coeff (401 + i) = 0 := S0_1_coeff_zero (401 + i) (by omega)
  have h2 : S0_2.coeff (401 + i) = 0 := S0_2_coeff_zero (401 + i) (by omega)
  have h3 : S0_3.coeff (401 + i) = 0 := S0_3_coeff_zero (401 + i) (by omega)
  have h4 : S0_4.coeff (401 + i) = 0 := S0_4_coeff_zero (401 + i) (by omega)
  have h5 : S0_5.coeff (401 + i) = S2560S0ShiftedPartsActual.R5.coeff i := by
    rw [S0_5_coeff, if_pos (by omega), show 401 + i - 401 = i from by omega]
  have h6 : S0_6.coeff (401 + i) = 0 := by
    rw [S0_6_coeff, if_neg (by omega)]
  have h7 : S0_7.coeff (401 + i) = 0 := by
    rw [S0_7_coeff, if_neg (by omega)]
  simp only [S0, coeff_add, h0, h1, h2, h3, h4, h5, h6, h7, zero_add, add_zero]

/-! ## The S0.coeff lookup table for 469 <= k <= 560 -/

lemma S0_coeff_469 : S0.coeff 469 = 187 := by
  exact (S0_coeff_block5 68 (by norm_num)).trans R5_coeff_68

lemma S0_coeff_470 : S0.coeff 470 = 262 := by
  exact (S0_coeff_block5 69 (by norm_num)).trans R5_coeff_69

lemma S0_coeff_471 : S0.coeff 471 = 202 := by
  exact (S0_coeff_block5 70 (by norm_num)).trans R5_coeff_70

lemma S0_coeff_472 : S0.coeff 472 = 408 := by
  exact (S0_coeff_block5 71 (by norm_num)).trans R5_coeff_71

lemma S0_coeff_473 : S0.coeff 473 = 469 := by
  exact (S0_coeff_block5 72 (by norm_num)).trans R5_coeff_72

lemma S0_coeff_474 : S0.coeff 474 = 210 := by
  exact (S0_coeff_block5 73 (by norm_num)).trans R5_coeff_73

lemma S0_coeff_475 : S0.coeff 475 = 306 := by
  exact (S0_coeff_block5 74 (by norm_num)).trans R5_coeff_74

lemma S0_coeff_476 : S0.coeff 476 = 172 := by
  exact (S0_coeff_block5 75 (by norm_num)).trans R5_coeff_75

lemma S0_coeff_477 : S0.coeff 477 = 427 := by
  exact (S0_coeff_block5 76 (by norm_num)).trans R5_coeff_76

lemma S0_coeff_478 : S0.coeff 478 = 261 := by
  exact (S0_coeff_block5 77 (by norm_num)).trans R5_coeff_77

lemma S0_coeff_479 : S0.coeff 479 = 482 := by
  exact (S0_coeff_block5 78 (by norm_num)).trans R5_coeff_78

lemma S0_coeff_480 : S0.coeff 480 = 172 := by
  exact (S0_coeff_block5 79 (by norm_num)).trans R5_coeff_79

lemma S0_coeff_481 : S0.coeff 481 = 20 := by
  exact (S0_coeff_block6 0 (by norm_num)).trans R6_coeff_0

lemma S0_coeff_482 : S0.coeff 482 = 409 := by
  exact (S0_coeff_block6 1 (by norm_num)).trans R6_coeff_1

lemma S0_coeff_483 : S0.coeff 483 = 107 := by
  exact (S0_coeff_block6 2 (by norm_num)).trans R6_coeff_2

lemma S0_coeff_484 : S0.coeff 484 = 89 := by
  exact (S0_coeff_block6 3 (by norm_num)).trans R6_coeff_3

lemma S0_coeff_485 : S0.coeff 485 = 93 := by
  exact (S0_coeff_block6 4 (by norm_num)).trans R6_coeff_4

lemma S0_coeff_486 : S0.coeff 486 = 55 := by
  exact (S0_coeff_block6 5 (by norm_num)).trans R6_coeff_5

lemma S0_coeff_487 : S0.coeff 487 = 464 := by
  exact (S0_coeff_block6 6 (by norm_num)).trans R6_coeff_6

lemma S0_coeff_488 : S0.coeff 488 = 427 := by
  exact (S0_coeff_block6 7 (by norm_num)).trans R6_coeff_7

lemma S0_coeff_489 : S0.coeff 489 = 339 := by
  exact (S0_coeff_block6 8 (by norm_num)).trans R6_coeff_8

lemma S0_coeff_490 : S0.coeff 490 = 194 := by
  exact (S0_coeff_block6 9 (by norm_num)).trans R6_coeff_9

lemma S0_coeff_491 : S0.coeff 491 = 205 := by
  exact (S0_coeff_block6 10 (by norm_num)).trans R6_coeff_10

lemma S0_coeff_492 : S0.coeff 492 = 482 := by
  exact (S0_coeff_block6 11 (by norm_num)).trans R6_coeff_11

lemma S0_coeff_493 : S0.coeff 493 = 573 := by
  exact (S0_coeff_block6 12 (by norm_num)).trans R6_coeff_12

lemma S0_coeff_494 : S0.coeff 494 = 129 := by
  exact (S0_coeff_block6 13 (by norm_num)).trans R6_coeff_13

lemma S0_coeff_495 : S0.coeff 495 = 451 := by
  exact (S0_coeff_block6 14 (by norm_num)).trans R6_coeff_14

lemma S0_coeff_496 : S0.coeff 496 = 334 := by
  exact (S0_coeff_block6 15 (by norm_num)).trans R6_coeff_15

lemma S0_coeff_497 : S0.coeff 497 = 342 := by
  exact (S0_coeff_block6 16 (by norm_num)).trans R6_coeff_16

lemma S0_coeff_498 : S0.coeff 498 = 113 := by
  exact (S0_coeff_block6 17 (by norm_num)).trans R6_coeff_17

lemma S0_coeff_499 : S0.coeff 499 = 435 := by
  exact (S0_coeff_block6 18 (by norm_num)).trans R6_coeff_18

lemma S0_coeff_500 : S0.coeff 500 = 163 := by
  exact (S0_coeff_block6 19 (by norm_num)).trans R6_coeff_19

lemma S0_coeff_501 : S0.coeff 501 = 520 := by
  exact (S0_coeff_block6 20 (by norm_num)).trans R6_coeff_20

lemma S0_coeff_502 : S0.coeff 502 = 103 := by
  exact (S0_coeff_block6 21 (by norm_num)).trans R6_coeff_21

lemma S0_coeff_503 : S0.coeff 503 = 338 := by
  exact (S0_coeff_block6 22 (by norm_num)).trans R6_coeff_22

lemma S0_coeff_504 : S0.coeff 504 = 450 := by
  exact (S0_coeff_block6 23 (by norm_num)).trans R6_coeff_23

lemma S0_coeff_505 : S0.coeff 505 = 390 := by
  exact (S0_coeff_block6 24 (by norm_num)).trans R6_coeff_24

lemma S0_coeff_506 : S0.coeff 506 = 362 := by
  exact (S0_coeff_block6 25 (by norm_num)).trans R6_coeff_25

lemma S0_coeff_507 : S0.coeff 507 = 336 := by
  exact (S0_coeff_block6 26 (by norm_num)).trans R6_coeff_26

lemma S0_coeff_508 : S0.coeff 508 = 83 := by
  exact (S0_coeff_block6 27 (by norm_num)).trans R6_coeff_27

lemma S0_coeff_509 : S0.coeff 509 = 295 := by
  exact (S0_coeff_block6 28 (by norm_num)).trans R6_coeff_28

lemma S0_coeff_510 : S0.coeff 510 = 359 := by
  exact (S0_coeff_block6 29 (by norm_num)).trans R6_coeff_29

lemma S0_coeff_511 : S0.coeff 511 = 9 := by
  exact (S0_coeff_block6 30 (by norm_num)).trans R6_coeff_30

lemma S0_coeff_512 : S0.coeff 512 = 314 := by
  exact (S0_coeff_block6 31 (by norm_num)).trans R6_coeff_31

lemma S0_coeff_513 : S0.coeff 513 = 504 := by
  exact (S0_coeff_block6 32 (by norm_num)).trans R6_coeff_32

lemma S0_coeff_514 : S0.coeff 514 = 433 := by
  exact (S0_coeff_block6 33 (by norm_num)).trans R6_coeff_33

lemma S0_coeff_515 : S0.coeff 515 = 212 := by
  exact (S0_coeff_block6 34 (by norm_num)).trans R6_coeff_34

lemma S0_coeff_516 : S0.coeff 516 = 419 := by
  exact (S0_coeff_block6 35 (by norm_num)).trans R6_coeff_35

lemma S0_coeff_517 : S0.coeff 517 = 34 := by
  exact (S0_coeff_block6 36 (by norm_num)).trans R6_coeff_36

lemma S0_coeff_518 : S0.coeff 518 = 307 := by
  exact (S0_coeff_block6 37 (by norm_num)).trans R6_coeff_37

lemma S0_coeff_519 : S0.coeff 519 = 313 := by
  exact (S0_coeff_block6 38 (by norm_num)).trans R6_coeff_38

lemma S0_coeff_520 : S0.coeff 520 = 11 := by
  exact (S0_coeff_block6 39 (by norm_num)).trans R6_coeff_39

lemma S0_coeff_521 : S0.coeff 521 = 266 := by
  exact (S0_coeff_block6 40 (by norm_num)).trans R6_coeff_40

lemma S0_coeff_522 : S0.coeff 522 = 242 := by
  exact (S0_coeff_block6 41 (by norm_num)).trans R6_coeff_41

lemma S0_coeff_523 : S0.coeff 523 = 270 := by
  exact (S0_coeff_block6 42 (by norm_num)).trans R6_coeff_42

lemma S0_coeff_524 : S0.coeff 524 = 605 := by
  exact (S0_coeff_block6 43 (by norm_num)).trans R6_coeff_43

lemma S0_coeff_525 : S0.coeff 525 = 128 := by
  exact (S0_coeff_block6 44 (by norm_num)).trans R6_coeff_44

lemma S0_coeff_526 : S0.coeff 526 = 362 := by
  exact (S0_coeff_block6 45 (by norm_num)).trans R6_coeff_45

lemma S0_coeff_527 : S0.coeff 527 = 488 := by
  exact (S0_coeff_block6 46 (by norm_num)).trans R6_coeff_46

lemma S0_coeff_528 : S0.coeff 528 = 253 := by
  exact (S0_coeff_block6 47 (by norm_num)).trans R6_coeff_47

lemma S0_coeff_529 : S0.coeff 529 = 56 := by
  exact (S0_coeff_block6 48 (by norm_num)).trans R6_coeff_48

lemma S0_coeff_530 : S0.coeff 530 = 327 := by
  exact (S0_coeff_block6 49 (by norm_num)).trans R6_coeff_49

lemma S0_coeff_531 : S0.coeff 531 = 7 := by
  exact (S0_coeff_block6 50 (by norm_num)).trans R6_coeff_50

lemma S0_coeff_532 : S0.coeff 532 = 301 := by
  exact (S0_coeff_block6 51 (by norm_num)).trans R6_coeff_51

lemma S0_coeff_533 : S0.coeff 533 = 522 := by
  exact (S0_coeff_block6 52 (by norm_num)).trans R6_coeff_52

lemma S0_coeff_534 : S0.coeff 534 = 430 := by
  exact (S0_coeff_block6 53 (by norm_num)).trans R6_coeff_53

lemma S0_coeff_535 : S0.coeff 535 = 581 := by
  exact (S0_coeff_block6 54 (by norm_num)).trans R6_coeff_54

lemma S0_coeff_536 : S0.coeff 536 = 546 := by
  exact (S0_coeff_block6 55 (by norm_num)).trans R6_coeff_55

lemma S0_coeff_537 : S0.coeff 537 = 591 := by
  exact (S0_coeff_block6 56 (by norm_num)).trans R6_coeff_56

lemma S0_coeff_538 : S0.coeff 538 = 329 := by
  exact (S0_coeff_block6 57 (by norm_num)).trans R6_coeff_57

lemma S0_coeff_539 : S0.coeff 539 = 286 := by
  exact (S0_coeff_block6 58 (by norm_num)).trans R6_coeff_58

lemma S0_coeff_540 : S0.coeff 540 = 446 := by
  exact (S0_coeff_block6 59 (by norm_num)).trans R6_coeff_59

lemma S0_coeff_541 : S0.coeff 541 = 307 := by
  exact (S0_coeff_block6 60 (by norm_num)).trans R6_coeff_60

lemma S0_coeff_542 : S0.coeff 542 = 96 := by
  exact (S0_coeff_block6 61 (by norm_num)).trans R6_coeff_61

lemma S0_coeff_543 : S0.coeff 543 = 199 := by
  exact (S0_coeff_block6 62 (by norm_num)).trans R6_coeff_62

lemma S0_coeff_544 : S0.coeff 544 = 565 := by
  exact (S0_coeff_block6 63 (by norm_num)).trans R6_coeff_63

lemma S0_coeff_545 : S0.coeff 545 = 25 := by
  exact (S0_coeff_block6 64 (by norm_num)).trans R6_coeff_64

lemma S0_coeff_546 : S0.coeff 546 = 589 := by
  exact (S0_coeff_block6 65 (by norm_num)).trans R6_coeff_65

lemma S0_coeff_547 : S0.coeff 547 = 609 := by
  exact (S0_coeff_block6 66 (by norm_num)).trans R6_coeff_66

lemma S0_coeff_548 : S0.coeff 548 = 241 := by
  exact (S0_coeff_block6 67 (by norm_num)).trans R6_coeff_67

lemma S0_coeff_549 : S0.coeff 549 = 277 := by
  exact (S0_coeff_block6 68 (by norm_num)).trans R6_coeff_68

lemma S0_coeff_550 : S0.coeff 550 = 499 := by
  exact (S0_coeff_block6 69 (by norm_num)).trans R6_coeff_69

lemma S0_coeff_551 : S0.coeff 551 = 445 := by
  exact (S0_coeff_block6 70 (by norm_num)).trans R6_coeff_70

lemma S0_coeff_552 : S0.coeff 552 = 297 := by
  exact (S0_coeff_block6 71 (by norm_num)).trans R6_coeff_71

lemma S0_coeff_553 : S0.coeff 553 = 281 := by
  exact (S0_coeff_block6 72 (by norm_num)).trans R6_coeff_72

lemma S0_coeff_554 : S0.coeff 554 = 378 := by
  exact (S0_coeff_block6 73 (by norm_num)).trans R6_coeff_73

lemma S0_coeff_555 : S0.coeff 555 = 417 := by
  exact (S0_coeff_block6 74 (by norm_num)).trans R6_coeff_74

lemma S0_coeff_556 : S0.coeff 556 = 168 := by
  exact (S0_coeff_block6 75 (by norm_num)).trans R6_coeff_75

lemma S0_coeff_557 : S0.coeff 557 = 591 := by
  exact (S0_coeff_block6 76 (by norm_num)).trans R6_coeff_76

lemma S0_coeff_558 : S0.coeff 558 = 56 := by
  exact (S0_coeff_block6 77 (by norm_num)).trans R6_coeff_77

lemma S0_coeff_559 : S0.coeff 559 = 227 := by
  exact (S0_coeff_block6 78 (by norm_num)).trans R6_coeff_78

lemma S0_coeff_560 : S0.coeff 560 = 272 := by
  exact (S0_coeff_block6 79 (by norm_num)).trans R6_coeff_79


/-! ## Coefficients of G and vanishing of T1 in the mid range -/

lemma G_coeff_0 : G.coeff 0 = 451 := by simp [G]
lemma G_coeff_1 : G.coeff 1 = 0 := by simp [G]
lemma G_coeff_2 : G.coeff 2 = 389 := by simp [G]
lemma G_coeff_3 : G.coeff 3 = 412 := by simp [G]
lemma G_coeff_4 : G.coeff 4 = 251 := by simp [G]
lemma G_coeff_5 : G.coeff 5 = 501 := by simp [G]
lemma G_coeff_6 : G.coeff 6 = 586 := by simp [G]
lemma G_coeff_7 : G.coeff 7 = 82 := by simp [G]
lemma G_coeff_8 : G.coeff 8 = 551 := by simp [G]
lemma G_coeff_9 : G.coeff 9 = 327 := by simp [G]
lemma G_coeff_10 : G.coeff 10 = 210 := by simp [G]
lemma G_coeff_11 : G.coeff 11 = 272 := by simp [G]
lemma G_coeff_12 : G.coeff 12 = 1 := by simp [G]

lemma X613_coeff_zero (n : ℕ) (hn : n < 613) :
    ((X : (ZMod 613)[X]) ^ 613).coeff n = 0 := by
  rw [coeff_X_pow]
  simp [show n ≠ 613 by omega]

lemma T1_coeff_zero (k : ℕ) (hk : 12 ≤ k) : T1.coeff k = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have h : T1.natDegree ≤ 11 := by unfold T1; compute_degree!
  omega

/-! ## The 80 target statements, n = 481 ... 560 -/

lemma chain1_coeff_481 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 481 = (G * S0).coeff 481 := by
  rw [G_mul_coeff_ge S0 481 (by norm_num), coeff_sub, X613_coeff_zero 481 (by norm_num),
    T1_coeff_zero 481 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_469, S0_coeff_470, S0_coeff_471, S0_coeff_472, S0_coeff_473, S0_coeff_474, S0_coeff_475, S0_coeff_476, S0_coeff_477, S0_coeff_478, S0_coeff_479, S0_coeff_480, S0_coeff_481]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_482 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 482 = (G * S0).coeff 482 := by
  rw [G_mul_coeff_ge S0 482 (by norm_num), coeff_sub, X613_coeff_zero 482 (by norm_num),
    T1_coeff_zero 482 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_470, S0_coeff_471, S0_coeff_472, S0_coeff_473, S0_coeff_474, S0_coeff_475, S0_coeff_476, S0_coeff_477, S0_coeff_478, S0_coeff_479, S0_coeff_480, S0_coeff_481, S0_coeff_482]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_483 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 483 = (G * S0).coeff 483 := by
  rw [G_mul_coeff_ge S0 483 (by norm_num), coeff_sub, X613_coeff_zero 483 (by norm_num),
    T1_coeff_zero 483 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_471, S0_coeff_472, S0_coeff_473, S0_coeff_474, S0_coeff_475, S0_coeff_476, S0_coeff_477, S0_coeff_478, S0_coeff_479, S0_coeff_480, S0_coeff_481, S0_coeff_482, S0_coeff_483]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_484 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 484 = (G * S0).coeff 484 := by
  rw [G_mul_coeff_ge S0 484 (by norm_num), coeff_sub, X613_coeff_zero 484 (by norm_num),
    T1_coeff_zero 484 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_472, S0_coeff_473, S0_coeff_474, S0_coeff_475, S0_coeff_476, S0_coeff_477, S0_coeff_478, S0_coeff_479, S0_coeff_480, S0_coeff_481, S0_coeff_482, S0_coeff_483, S0_coeff_484]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_485 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 485 = (G * S0).coeff 485 := by
  rw [G_mul_coeff_ge S0 485 (by norm_num), coeff_sub, X613_coeff_zero 485 (by norm_num),
    T1_coeff_zero 485 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_473, S0_coeff_474, S0_coeff_475, S0_coeff_476, S0_coeff_477, S0_coeff_478, S0_coeff_479, S0_coeff_480, S0_coeff_481, S0_coeff_482, S0_coeff_483, S0_coeff_484, S0_coeff_485]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_486 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 486 = (G * S0).coeff 486 := by
  rw [G_mul_coeff_ge S0 486 (by norm_num), coeff_sub, X613_coeff_zero 486 (by norm_num),
    T1_coeff_zero 486 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_474, S0_coeff_475, S0_coeff_476, S0_coeff_477, S0_coeff_478, S0_coeff_479, S0_coeff_480, S0_coeff_481, S0_coeff_482, S0_coeff_483, S0_coeff_484, S0_coeff_485, S0_coeff_486]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_487 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 487 = (G * S0).coeff 487 := by
  rw [G_mul_coeff_ge S0 487 (by norm_num), coeff_sub, X613_coeff_zero 487 (by norm_num),
    T1_coeff_zero 487 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_475, S0_coeff_476, S0_coeff_477, S0_coeff_478, S0_coeff_479, S0_coeff_480, S0_coeff_481, S0_coeff_482, S0_coeff_483, S0_coeff_484, S0_coeff_485, S0_coeff_486, S0_coeff_487]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_488 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 488 = (G * S0).coeff 488 := by
  rw [G_mul_coeff_ge S0 488 (by norm_num), coeff_sub, X613_coeff_zero 488 (by norm_num),
    T1_coeff_zero 488 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_476, S0_coeff_477, S0_coeff_478, S0_coeff_479, S0_coeff_480, S0_coeff_481, S0_coeff_482, S0_coeff_483, S0_coeff_484, S0_coeff_485, S0_coeff_486, S0_coeff_487, S0_coeff_488]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_489 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 489 = (G * S0).coeff 489 := by
  rw [G_mul_coeff_ge S0 489 (by norm_num), coeff_sub, X613_coeff_zero 489 (by norm_num),
    T1_coeff_zero 489 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_477, S0_coeff_478, S0_coeff_479, S0_coeff_480, S0_coeff_481, S0_coeff_482, S0_coeff_483, S0_coeff_484, S0_coeff_485, S0_coeff_486, S0_coeff_487, S0_coeff_488, S0_coeff_489]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_490 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 490 = (G * S0).coeff 490 := by
  rw [G_mul_coeff_ge S0 490 (by norm_num), coeff_sub, X613_coeff_zero 490 (by norm_num),
    T1_coeff_zero 490 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_478, S0_coeff_479, S0_coeff_480, S0_coeff_481, S0_coeff_482, S0_coeff_483, S0_coeff_484, S0_coeff_485, S0_coeff_486, S0_coeff_487, S0_coeff_488, S0_coeff_489, S0_coeff_490]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_491 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 491 = (G * S0).coeff 491 := by
  rw [G_mul_coeff_ge S0 491 (by norm_num), coeff_sub, X613_coeff_zero 491 (by norm_num),
    T1_coeff_zero 491 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_479, S0_coeff_480, S0_coeff_481, S0_coeff_482, S0_coeff_483, S0_coeff_484, S0_coeff_485, S0_coeff_486, S0_coeff_487, S0_coeff_488, S0_coeff_489, S0_coeff_490, S0_coeff_491]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_492 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 492 = (G * S0).coeff 492 := by
  rw [G_mul_coeff_ge S0 492 (by norm_num), coeff_sub, X613_coeff_zero 492 (by norm_num),
    T1_coeff_zero 492 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_480, S0_coeff_481, S0_coeff_482, S0_coeff_483, S0_coeff_484, S0_coeff_485, S0_coeff_486, S0_coeff_487, S0_coeff_488, S0_coeff_489, S0_coeff_490, S0_coeff_491, S0_coeff_492]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_493 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 493 = (G * S0).coeff 493 := by
  rw [G_mul_coeff_ge S0 493 (by norm_num), coeff_sub, X613_coeff_zero 493 (by norm_num),
    T1_coeff_zero 493 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_481, S0_coeff_482, S0_coeff_483, S0_coeff_484, S0_coeff_485, S0_coeff_486, S0_coeff_487, S0_coeff_488, S0_coeff_489, S0_coeff_490, S0_coeff_491, S0_coeff_492, S0_coeff_493]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_494 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 494 = (G * S0).coeff 494 := by
  rw [G_mul_coeff_ge S0 494 (by norm_num), coeff_sub, X613_coeff_zero 494 (by norm_num),
    T1_coeff_zero 494 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_482, S0_coeff_483, S0_coeff_484, S0_coeff_485, S0_coeff_486, S0_coeff_487, S0_coeff_488, S0_coeff_489, S0_coeff_490, S0_coeff_491, S0_coeff_492, S0_coeff_493, S0_coeff_494]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_495 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 495 = (G * S0).coeff 495 := by
  rw [G_mul_coeff_ge S0 495 (by norm_num), coeff_sub, X613_coeff_zero 495 (by norm_num),
    T1_coeff_zero 495 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_483, S0_coeff_484, S0_coeff_485, S0_coeff_486, S0_coeff_487, S0_coeff_488, S0_coeff_489, S0_coeff_490, S0_coeff_491, S0_coeff_492, S0_coeff_493, S0_coeff_494, S0_coeff_495]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_496 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 496 = (G * S0).coeff 496 := by
  rw [G_mul_coeff_ge S0 496 (by norm_num), coeff_sub, X613_coeff_zero 496 (by norm_num),
    T1_coeff_zero 496 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_484, S0_coeff_485, S0_coeff_486, S0_coeff_487, S0_coeff_488, S0_coeff_489, S0_coeff_490, S0_coeff_491, S0_coeff_492, S0_coeff_493, S0_coeff_494, S0_coeff_495, S0_coeff_496]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_497 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 497 = (G * S0).coeff 497 := by
  rw [G_mul_coeff_ge S0 497 (by norm_num), coeff_sub, X613_coeff_zero 497 (by norm_num),
    T1_coeff_zero 497 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_485, S0_coeff_486, S0_coeff_487, S0_coeff_488, S0_coeff_489, S0_coeff_490, S0_coeff_491, S0_coeff_492, S0_coeff_493, S0_coeff_494, S0_coeff_495, S0_coeff_496, S0_coeff_497]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_498 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 498 = (G * S0).coeff 498 := by
  rw [G_mul_coeff_ge S0 498 (by norm_num), coeff_sub, X613_coeff_zero 498 (by norm_num),
    T1_coeff_zero 498 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_486, S0_coeff_487, S0_coeff_488, S0_coeff_489, S0_coeff_490, S0_coeff_491, S0_coeff_492, S0_coeff_493, S0_coeff_494, S0_coeff_495, S0_coeff_496, S0_coeff_497, S0_coeff_498]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_499 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 499 = (G * S0).coeff 499 := by
  rw [G_mul_coeff_ge S0 499 (by norm_num), coeff_sub, X613_coeff_zero 499 (by norm_num),
    T1_coeff_zero 499 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_487, S0_coeff_488, S0_coeff_489, S0_coeff_490, S0_coeff_491, S0_coeff_492, S0_coeff_493, S0_coeff_494, S0_coeff_495, S0_coeff_496, S0_coeff_497, S0_coeff_498, S0_coeff_499]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_500 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 500 = (G * S0).coeff 500 := by
  rw [G_mul_coeff_ge S0 500 (by norm_num), coeff_sub, X613_coeff_zero 500 (by norm_num),
    T1_coeff_zero 500 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_488, S0_coeff_489, S0_coeff_490, S0_coeff_491, S0_coeff_492, S0_coeff_493, S0_coeff_494, S0_coeff_495, S0_coeff_496, S0_coeff_497, S0_coeff_498, S0_coeff_499, S0_coeff_500]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_501 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 501 = (G * S0).coeff 501 := by
  rw [G_mul_coeff_ge S0 501 (by norm_num), coeff_sub, X613_coeff_zero 501 (by norm_num),
    T1_coeff_zero 501 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_489, S0_coeff_490, S0_coeff_491, S0_coeff_492, S0_coeff_493, S0_coeff_494, S0_coeff_495, S0_coeff_496, S0_coeff_497, S0_coeff_498, S0_coeff_499, S0_coeff_500, S0_coeff_501]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_502 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 502 = (G * S0).coeff 502 := by
  rw [G_mul_coeff_ge S0 502 (by norm_num), coeff_sub, X613_coeff_zero 502 (by norm_num),
    T1_coeff_zero 502 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_490, S0_coeff_491, S0_coeff_492, S0_coeff_493, S0_coeff_494, S0_coeff_495, S0_coeff_496, S0_coeff_497, S0_coeff_498, S0_coeff_499, S0_coeff_500, S0_coeff_501, S0_coeff_502]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_503 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 503 = (G * S0).coeff 503 := by
  rw [G_mul_coeff_ge S0 503 (by norm_num), coeff_sub, X613_coeff_zero 503 (by norm_num),
    T1_coeff_zero 503 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_491, S0_coeff_492, S0_coeff_493, S0_coeff_494, S0_coeff_495, S0_coeff_496, S0_coeff_497, S0_coeff_498, S0_coeff_499, S0_coeff_500, S0_coeff_501, S0_coeff_502, S0_coeff_503]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_504 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 504 = (G * S0).coeff 504 := by
  rw [G_mul_coeff_ge S0 504 (by norm_num), coeff_sub, X613_coeff_zero 504 (by norm_num),
    T1_coeff_zero 504 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_492, S0_coeff_493, S0_coeff_494, S0_coeff_495, S0_coeff_496, S0_coeff_497, S0_coeff_498, S0_coeff_499, S0_coeff_500, S0_coeff_501, S0_coeff_502, S0_coeff_503, S0_coeff_504]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_505 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 505 = (G * S0).coeff 505 := by
  rw [G_mul_coeff_ge S0 505 (by norm_num), coeff_sub, X613_coeff_zero 505 (by norm_num),
    T1_coeff_zero 505 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_493, S0_coeff_494, S0_coeff_495, S0_coeff_496, S0_coeff_497, S0_coeff_498, S0_coeff_499, S0_coeff_500, S0_coeff_501, S0_coeff_502, S0_coeff_503, S0_coeff_504, S0_coeff_505]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_506 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 506 = (G * S0).coeff 506 := by
  rw [G_mul_coeff_ge S0 506 (by norm_num), coeff_sub, X613_coeff_zero 506 (by norm_num),
    T1_coeff_zero 506 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_494, S0_coeff_495, S0_coeff_496, S0_coeff_497, S0_coeff_498, S0_coeff_499, S0_coeff_500, S0_coeff_501, S0_coeff_502, S0_coeff_503, S0_coeff_504, S0_coeff_505, S0_coeff_506]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_507 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 507 = (G * S0).coeff 507 := by
  rw [G_mul_coeff_ge S0 507 (by norm_num), coeff_sub, X613_coeff_zero 507 (by norm_num),
    T1_coeff_zero 507 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_495, S0_coeff_496, S0_coeff_497, S0_coeff_498, S0_coeff_499, S0_coeff_500, S0_coeff_501, S0_coeff_502, S0_coeff_503, S0_coeff_504, S0_coeff_505, S0_coeff_506, S0_coeff_507]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_508 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 508 = (G * S0).coeff 508 := by
  rw [G_mul_coeff_ge S0 508 (by norm_num), coeff_sub, X613_coeff_zero 508 (by norm_num),
    T1_coeff_zero 508 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_496, S0_coeff_497, S0_coeff_498, S0_coeff_499, S0_coeff_500, S0_coeff_501, S0_coeff_502, S0_coeff_503, S0_coeff_504, S0_coeff_505, S0_coeff_506, S0_coeff_507, S0_coeff_508]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_509 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 509 = (G * S0).coeff 509 := by
  rw [G_mul_coeff_ge S0 509 (by norm_num), coeff_sub, X613_coeff_zero 509 (by norm_num),
    T1_coeff_zero 509 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_497, S0_coeff_498, S0_coeff_499, S0_coeff_500, S0_coeff_501, S0_coeff_502, S0_coeff_503, S0_coeff_504, S0_coeff_505, S0_coeff_506, S0_coeff_507, S0_coeff_508, S0_coeff_509]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_510 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 510 = (G * S0).coeff 510 := by
  rw [G_mul_coeff_ge S0 510 (by norm_num), coeff_sub, X613_coeff_zero 510 (by norm_num),
    T1_coeff_zero 510 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_498, S0_coeff_499, S0_coeff_500, S0_coeff_501, S0_coeff_502, S0_coeff_503, S0_coeff_504, S0_coeff_505, S0_coeff_506, S0_coeff_507, S0_coeff_508, S0_coeff_509, S0_coeff_510]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_511 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 511 = (G * S0).coeff 511 := by
  rw [G_mul_coeff_ge S0 511 (by norm_num), coeff_sub, X613_coeff_zero 511 (by norm_num),
    T1_coeff_zero 511 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_499, S0_coeff_500, S0_coeff_501, S0_coeff_502, S0_coeff_503, S0_coeff_504, S0_coeff_505, S0_coeff_506, S0_coeff_507, S0_coeff_508, S0_coeff_509, S0_coeff_510, S0_coeff_511]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_512 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 512 = (G * S0).coeff 512 := by
  rw [G_mul_coeff_ge S0 512 (by norm_num), coeff_sub, X613_coeff_zero 512 (by norm_num),
    T1_coeff_zero 512 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_500, S0_coeff_501, S0_coeff_502, S0_coeff_503, S0_coeff_504, S0_coeff_505, S0_coeff_506, S0_coeff_507, S0_coeff_508, S0_coeff_509, S0_coeff_510, S0_coeff_511, S0_coeff_512]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_513 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 513 = (G * S0).coeff 513 := by
  rw [G_mul_coeff_ge S0 513 (by norm_num), coeff_sub, X613_coeff_zero 513 (by norm_num),
    T1_coeff_zero 513 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_501, S0_coeff_502, S0_coeff_503, S0_coeff_504, S0_coeff_505, S0_coeff_506, S0_coeff_507, S0_coeff_508, S0_coeff_509, S0_coeff_510, S0_coeff_511, S0_coeff_512, S0_coeff_513]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_514 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 514 = (G * S0).coeff 514 := by
  rw [G_mul_coeff_ge S0 514 (by norm_num), coeff_sub, X613_coeff_zero 514 (by norm_num),
    T1_coeff_zero 514 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_502, S0_coeff_503, S0_coeff_504, S0_coeff_505, S0_coeff_506, S0_coeff_507, S0_coeff_508, S0_coeff_509, S0_coeff_510, S0_coeff_511, S0_coeff_512, S0_coeff_513, S0_coeff_514]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_515 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 515 = (G * S0).coeff 515 := by
  rw [G_mul_coeff_ge S0 515 (by norm_num), coeff_sub, X613_coeff_zero 515 (by norm_num),
    T1_coeff_zero 515 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_503, S0_coeff_504, S0_coeff_505, S0_coeff_506, S0_coeff_507, S0_coeff_508, S0_coeff_509, S0_coeff_510, S0_coeff_511, S0_coeff_512, S0_coeff_513, S0_coeff_514, S0_coeff_515]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_516 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 516 = (G * S0).coeff 516 := by
  rw [G_mul_coeff_ge S0 516 (by norm_num), coeff_sub, X613_coeff_zero 516 (by norm_num),
    T1_coeff_zero 516 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_504, S0_coeff_505, S0_coeff_506, S0_coeff_507, S0_coeff_508, S0_coeff_509, S0_coeff_510, S0_coeff_511, S0_coeff_512, S0_coeff_513, S0_coeff_514, S0_coeff_515, S0_coeff_516]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_517 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 517 = (G * S0).coeff 517 := by
  rw [G_mul_coeff_ge S0 517 (by norm_num), coeff_sub, X613_coeff_zero 517 (by norm_num),
    T1_coeff_zero 517 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_505, S0_coeff_506, S0_coeff_507, S0_coeff_508, S0_coeff_509, S0_coeff_510, S0_coeff_511, S0_coeff_512, S0_coeff_513, S0_coeff_514, S0_coeff_515, S0_coeff_516, S0_coeff_517]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_518 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 518 = (G * S0).coeff 518 := by
  rw [G_mul_coeff_ge S0 518 (by norm_num), coeff_sub, X613_coeff_zero 518 (by norm_num),
    T1_coeff_zero 518 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_506, S0_coeff_507, S0_coeff_508, S0_coeff_509, S0_coeff_510, S0_coeff_511, S0_coeff_512, S0_coeff_513, S0_coeff_514, S0_coeff_515, S0_coeff_516, S0_coeff_517, S0_coeff_518]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_519 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 519 = (G * S0).coeff 519 := by
  rw [G_mul_coeff_ge S0 519 (by norm_num), coeff_sub, X613_coeff_zero 519 (by norm_num),
    T1_coeff_zero 519 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_507, S0_coeff_508, S0_coeff_509, S0_coeff_510, S0_coeff_511, S0_coeff_512, S0_coeff_513, S0_coeff_514, S0_coeff_515, S0_coeff_516, S0_coeff_517, S0_coeff_518, S0_coeff_519]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_520 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 520 = (G * S0).coeff 520 := by
  rw [G_mul_coeff_ge S0 520 (by norm_num), coeff_sub, X613_coeff_zero 520 (by norm_num),
    T1_coeff_zero 520 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_508, S0_coeff_509, S0_coeff_510, S0_coeff_511, S0_coeff_512, S0_coeff_513, S0_coeff_514, S0_coeff_515, S0_coeff_516, S0_coeff_517, S0_coeff_518, S0_coeff_519, S0_coeff_520]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_521 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 521 = (G * S0).coeff 521 := by
  rw [G_mul_coeff_ge S0 521 (by norm_num), coeff_sub, X613_coeff_zero 521 (by norm_num),
    T1_coeff_zero 521 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_509, S0_coeff_510, S0_coeff_511, S0_coeff_512, S0_coeff_513, S0_coeff_514, S0_coeff_515, S0_coeff_516, S0_coeff_517, S0_coeff_518, S0_coeff_519, S0_coeff_520, S0_coeff_521]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_522 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 522 = (G * S0).coeff 522 := by
  rw [G_mul_coeff_ge S0 522 (by norm_num), coeff_sub, X613_coeff_zero 522 (by norm_num),
    T1_coeff_zero 522 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_510, S0_coeff_511, S0_coeff_512, S0_coeff_513, S0_coeff_514, S0_coeff_515, S0_coeff_516, S0_coeff_517, S0_coeff_518, S0_coeff_519, S0_coeff_520, S0_coeff_521, S0_coeff_522]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_523 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 523 = (G * S0).coeff 523 := by
  rw [G_mul_coeff_ge S0 523 (by norm_num), coeff_sub, X613_coeff_zero 523 (by norm_num),
    T1_coeff_zero 523 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_511, S0_coeff_512, S0_coeff_513, S0_coeff_514, S0_coeff_515, S0_coeff_516, S0_coeff_517, S0_coeff_518, S0_coeff_519, S0_coeff_520, S0_coeff_521, S0_coeff_522, S0_coeff_523]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_524 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 524 = (G * S0).coeff 524 := by
  rw [G_mul_coeff_ge S0 524 (by norm_num), coeff_sub, X613_coeff_zero 524 (by norm_num),
    T1_coeff_zero 524 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_512, S0_coeff_513, S0_coeff_514, S0_coeff_515, S0_coeff_516, S0_coeff_517, S0_coeff_518, S0_coeff_519, S0_coeff_520, S0_coeff_521, S0_coeff_522, S0_coeff_523, S0_coeff_524]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_525 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 525 = (G * S0).coeff 525 := by
  rw [G_mul_coeff_ge S0 525 (by norm_num), coeff_sub, X613_coeff_zero 525 (by norm_num),
    T1_coeff_zero 525 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_513, S0_coeff_514, S0_coeff_515, S0_coeff_516, S0_coeff_517, S0_coeff_518, S0_coeff_519, S0_coeff_520, S0_coeff_521, S0_coeff_522, S0_coeff_523, S0_coeff_524, S0_coeff_525]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_526 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 526 = (G * S0).coeff 526 := by
  rw [G_mul_coeff_ge S0 526 (by norm_num), coeff_sub, X613_coeff_zero 526 (by norm_num),
    T1_coeff_zero 526 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_514, S0_coeff_515, S0_coeff_516, S0_coeff_517, S0_coeff_518, S0_coeff_519, S0_coeff_520, S0_coeff_521, S0_coeff_522, S0_coeff_523, S0_coeff_524, S0_coeff_525, S0_coeff_526]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_527 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 527 = (G * S0).coeff 527 := by
  rw [G_mul_coeff_ge S0 527 (by norm_num), coeff_sub, X613_coeff_zero 527 (by norm_num),
    T1_coeff_zero 527 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_515, S0_coeff_516, S0_coeff_517, S0_coeff_518, S0_coeff_519, S0_coeff_520, S0_coeff_521, S0_coeff_522, S0_coeff_523, S0_coeff_524, S0_coeff_525, S0_coeff_526, S0_coeff_527]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_528 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 528 = (G * S0).coeff 528 := by
  rw [G_mul_coeff_ge S0 528 (by norm_num), coeff_sub, X613_coeff_zero 528 (by norm_num),
    T1_coeff_zero 528 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_516, S0_coeff_517, S0_coeff_518, S0_coeff_519, S0_coeff_520, S0_coeff_521, S0_coeff_522, S0_coeff_523, S0_coeff_524, S0_coeff_525, S0_coeff_526, S0_coeff_527, S0_coeff_528]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_529 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 529 = (G * S0).coeff 529 := by
  rw [G_mul_coeff_ge S0 529 (by norm_num), coeff_sub, X613_coeff_zero 529 (by norm_num),
    T1_coeff_zero 529 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_517, S0_coeff_518, S0_coeff_519, S0_coeff_520, S0_coeff_521, S0_coeff_522, S0_coeff_523, S0_coeff_524, S0_coeff_525, S0_coeff_526, S0_coeff_527, S0_coeff_528, S0_coeff_529]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_530 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 530 = (G * S0).coeff 530 := by
  rw [G_mul_coeff_ge S0 530 (by norm_num), coeff_sub, X613_coeff_zero 530 (by norm_num),
    T1_coeff_zero 530 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_518, S0_coeff_519, S0_coeff_520, S0_coeff_521, S0_coeff_522, S0_coeff_523, S0_coeff_524, S0_coeff_525, S0_coeff_526, S0_coeff_527, S0_coeff_528, S0_coeff_529, S0_coeff_530]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_531 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 531 = (G * S0).coeff 531 := by
  rw [G_mul_coeff_ge S0 531 (by norm_num), coeff_sub, X613_coeff_zero 531 (by norm_num),
    T1_coeff_zero 531 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_519, S0_coeff_520, S0_coeff_521, S0_coeff_522, S0_coeff_523, S0_coeff_524, S0_coeff_525, S0_coeff_526, S0_coeff_527, S0_coeff_528, S0_coeff_529, S0_coeff_530, S0_coeff_531]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_532 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 532 = (G * S0).coeff 532 := by
  rw [G_mul_coeff_ge S0 532 (by norm_num), coeff_sub, X613_coeff_zero 532 (by norm_num),
    T1_coeff_zero 532 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_520, S0_coeff_521, S0_coeff_522, S0_coeff_523, S0_coeff_524, S0_coeff_525, S0_coeff_526, S0_coeff_527, S0_coeff_528, S0_coeff_529, S0_coeff_530, S0_coeff_531, S0_coeff_532]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_533 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 533 = (G * S0).coeff 533 := by
  rw [G_mul_coeff_ge S0 533 (by norm_num), coeff_sub, X613_coeff_zero 533 (by norm_num),
    T1_coeff_zero 533 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_521, S0_coeff_522, S0_coeff_523, S0_coeff_524, S0_coeff_525, S0_coeff_526, S0_coeff_527, S0_coeff_528, S0_coeff_529, S0_coeff_530, S0_coeff_531, S0_coeff_532, S0_coeff_533]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_534 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 534 = (G * S0).coeff 534 := by
  rw [G_mul_coeff_ge S0 534 (by norm_num), coeff_sub, X613_coeff_zero 534 (by norm_num),
    T1_coeff_zero 534 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_522, S0_coeff_523, S0_coeff_524, S0_coeff_525, S0_coeff_526, S0_coeff_527, S0_coeff_528, S0_coeff_529, S0_coeff_530, S0_coeff_531, S0_coeff_532, S0_coeff_533, S0_coeff_534]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_535 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 535 = (G * S0).coeff 535 := by
  rw [G_mul_coeff_ge S0 535 (by norm_num), coeff_sub, X613_coeff_zero 535 (by norm_num),
    T1_coeff_zero 535 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_523, S0_coeff_524, S0_coeff_525, S0_coeff_526, S0_coeff_527, S0_coeff_528, S0_coeff_529, S0_coeff_530, S0_coeff_531, S0_coeff_532, S0_coeff_533, S0_coeff_534, S0_coeff_535]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_536 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 536 = (G * S0).coeff 536 := by
  rw [G_mul_coeff_ge S0 536 (by norm_num), coeff_sub, X613_coeff_zero 536 (by norm_num),
    T1_coeff_zero 536 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_524, S0_coeff_525, S0_coeff_526, S0_coeff_527, S0_coeff_528, S0_coeff_529, S0_coeff_530, S0_coeff_531, S0_coeff_532, S0_coeff_533, S0_coeff_534, S0_coeff_535, S0_coeff_536]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_537 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 537 = (G * S0).coeff 537 := by
  rw [G_mul_coeff_ge S0 537 (by norm_num), coeff_sub, X613_coeff_zero 537 (by norm_num),
    T1_coeff_zero 537 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_525, S0_coeff_526, S0_coeff_527, S0_coeff_528, S0_coeff_529, S0_coeff_530, S0_coeff_531, S0_coeff_532, S0_coeff_533, S0_coeff_534, S0_coeff_535, S0_coeff_536, S0_coeff_537]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_538 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 538 = (G * S0).coeff 538 := by
  rw [G_mul_coeff_ge S0 538 (by norm_num), coeff_sub, X613_coeff_zero 538 (by norm_num),
    T1_coeff_zero 538 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_526, S0_coeff_527, S0_coeff_528, S0_coeff_529, S0_coeff_530, S0_coeff_531, S0_coeff_532, S0_coeff_533, S0_coeff_534, S0_coeff_535, S0_coeff_536, S0_coeff_537, S0_coeff_538]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_539 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 539 = (G * S0).coeff 539 := by
  rw [G_mul_coeff_ge S0 539 (by norm_num), coeff_sub, X613_coeff_zero 539 (by norm_num),
    T1_coeff_zero 539 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_527, S0_coeff_528, S0_coeff_529, S0_coeff_530, S0_coeff_531, S0_coeff_532, S0_coeff_533, S0_coeff_534, S0_coeff_535, S0_coeff_536, S0_coeff_537, S0_coeff_538, S0_coeff_539]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_540 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 540 = (G * S0).coeff 540 := by
  rw [G_mul_coeff_ge S0 540 (by norm_num), coeff_sub, X613_coeff_zero 540 (by norm_num),
    T1_coeff_zero 540 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_528, S0_coeff_529, S0_coeff_530, S0_coeff_531, S0_coeff_532, S0_coeff_533, S0_coeff_534, S0_coeff_535, S0_coeff_536, S0_coeff_537, S0_coeff_538, S0_coeff_539, S0_coeff_540]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_541 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 541 = (G * S0).coeff 541 := by
  rw [G_mul_coeff_ge S0 541 (by norm_num), coeff_sub, X613_coeff_zero 541 (by norm_num),
    T1_coeff_zero 541 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_529, S0_coeff_530, S0_coeff_531, S0_coeff_532, S0_coeff_533, S0_coeff_534, S0_coeff_535, S0_coeff_536, S0_coeff_537, S0_coeff_538, S0_coeff_539, S0_coeff_540, S0_coeff_541]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_542 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 542 = (G * S0).coeff 542 := by
  rw [G_mul_coeff_ge S0 542 (by norm_num), coeff_sub, X613_coeff_zero 542 (by norm_num),
    T1_coeff_zero 542 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_530, S0_coeff_531, S0_coeff_532, S0_coeff_533, S0_coeff_534, S0_coeff_535, S0_coeff_536, S0_coeff_537, S0_coeff_538, S0_coeff_539, S0_coeff_540, S0_coeff_541, S0_coeff_542]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_543 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 543 = (G * S0).coeff 543 := by
  rw [G_mul_coeff_ge S0 543 (by norm_num), coeff_sub, X613_coeff_zero 543 (by norm_num),
    T1_coeff_zero 543 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_531, S0_coeff_532, S0_coeff_533, S0_coeff_534, S0_coeff_535, S0_coeff_536, S0_coeff_537, S0_coeff_538, S0_coeff_539, S0_coeff_540, S0_coeff_541, S0_coeff_542, S0_coeff_543]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_544 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 544 = (G * S0).coeff 544 := by
  rw [G_mul_coeff_ge S0 544 (by norm_num), coeff_sub, X613_coeff_zero 544 (by norm_num),
    T1_coeff_zero 544 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_532, S0_coeff_533, S0_coeff_534, S0_coeff_535, S0_coeff_536, S0_coeff_537, S0_coeff_538, S0_coeff_539, S0_coeff_540, S0_coeff_541, S0_coeff_542, S0_coeff_543, S0_coeff_544]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_545 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 545 = (G * S0).coeff 545 := by
  rw [G_mul_coeff_ge S0 545 (by norm_num), coeff_sub, X613_coeff_zero 545 (by norm_num),
    T1_coeff_zero 545 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_533, S0_coeff_534, S0_coeff_535, S0_coeff_536, S0_coeff_537, S0_coeff_538, S0_coeff_539, S0_coeff_540, S0_coeff_541, S0_coeff_542, S0_coeff_543, S0_coeff_544, S0_coeff_545]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_546 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 546 = (G * S0).coeff 546 := by
  rw [G_mul_coeff_ge S0 546 (by norm_num), coeff_sub, X613_coeff_zero 546 (by norm_num),
    T1_coeff_zero 546 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_534, S0_coeff_535, S0_coeff_536, S0_coeff_537, S0_coeff_538, S0_coeff_539, S0_coeff_540, S0_coeff_541, S0_coeff_542, S0_coeff_543, S0_coeff_544, S0_coeff_545, S0_coeff_546]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_547 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 547 = (G * S0).coeff 547 := by
  rw [G_mul_coeff_ge S0 547 (by norm_num), coeff_sub, X613_coeff_zero 547 (by norm_num),
    T1_coeff_zero 547 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_535, S0_coeff_536, S0_coeff_537, S0_coeff_538, S0_coeff_539, S0_coeff_540, S0_coeff_541, S0_coeff_542, S0_coeff_543, S0_coeff_544, S0_coeff_545, S0_coeff_546, S0_coeff_547]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_548 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 548 = (G * S0).coeff 548 := by
  rw [G_mul_coeff_ge S0 548 (by norm_num), coeff_sub, X613_coeff_zero 548 (by norm_num),
    T1_coeff_zero 548 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_536, S0_coeff_537, S0_coeff_538, S0_coeff_539, S0_coeff_540, S0_coeff_541, S0_coeff_542, S0_coeff_543, S0_coeff_544, S0_coeff_545, S0_coeff_546, S0_coeff_547, S0_coeff_548]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_549 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 549 = (G * S0).coeff 549 := by
  rw [G_mul_coeff_ge S0 549 (by norm_num), coeff_sub, X613_coeff_zero 549 (by norm_num),
    T1_coeff_zero 549 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_537, S0_coeff_538, S0_coeff_539, S0_coeff_540, S0_coeff_541, S0_coeff_542, S0_coeff_543, S0_coeff_544, S0_coeff_545, S0_coeff_546, S0_coeff_547, S0_coeff_548, S0_coeff_549]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_550 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 550 = (G * S0).coeff 550 := by
  rw [G_mul_coeff_ge S0 550 (by norm_num), coeff_sub, X613_coeff_zero 550 (by norm_num),
    T1_coeff_zero 550 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_538, S0_coeff_539, S0_coeff_540, S0_coeff_541, S0_coeff_542, S0_coeff_543, S0_coeff_544, S0_coeff_545, S0_coeff_546, S0_coeff_547, S0_coeff_548, S0_coeff_549, S0_coeff_550]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_551 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 551 = (G * S0).coeff 551 := by
  rw [G_mul_coeff_ge S0 551 (by norm_num), coeff_sub, X613_coeff_zero 551 (by norm_num),
    T1_coeff_zero 551 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_539, S0_coeff_540, S0_coeff_541, S0_coeff_542, S0_coeff_543, S0_coeff_544, S0_coeff_545, S0_coeff_546, S0_coeff_547, S0_coeff_548, S0_coeff_549, S0_coeff_550, S0_coeff_551]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_552 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 552 = (G * S0).coeff 552 := by
  rw [G_mul_coeff_ge S0 552 (by norm_num), coeff_sub, X613_coeff_zero 552 (by norm_num),
    T1_coeff_zero 552 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_540, S0_coeff_541, S0_coeff_542, S0_coeff_543, S0_coeff_544, S0_coeff_545, S0_coeff_546, S0_coeff_547, S0_coeff_548, S0_coeff_549, S0_coeff_550, S0_coeff_551, S0_coeff_552]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_553 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 553 = (G * S0).coeff 553 := by
  rw [G_mul_coeff_ge S0 553 (by norm_num), coeff_sub, X613_coeff_zero 553 (by norm_num),
    T1_coeff_zero 553 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_541, S0_coeff_542, S0_coeff_543, S0_coeff_544, S0_coeff_545, S0_coeff_546, S0_coeff_547, S0_coeff_548, S0_coeff_549, S0_coeff_550, S0_coeff_551, S0_coeff_552, S0_coeff_553]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_554 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 554 = (G * S0).coeff 554 := by
  rw [G_mul_coeff_ge S0 554 (by norm_num), coeff_sub, X613_coeff_zero 554 (by norm_num),
    T1_coeff_zero 554 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_542, S0_coeff_543, S0_coeff_544, S0_coeff_545, S0_coeff_546, S0_coeff_547, S0_coeff_548, S0_coeff_549, S0_coeff_550, S0_coeff_551, S0_coeff_552, S0_coeff_553, S0_coeff_554]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_555 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 555 = (G * S0).coeff 555 := by
  rw [G_mul_coeff_ge S0 555 (by norm_num), coeff_sub, X613_coeff_zero 555 (by norm_num),
    T1_coeff_zero 555 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_543, S0_coeff_544, S0_coeff_545, S0_coeff_546, S0_coeff_547, S0_coeff_548, S0_coeff_549, S0_coeff_550, S0_coeff_551, S0_coeff_552, S0_coeff_553, S0_coeff_554, S0_coeff_555]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_556 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 556 = (G * S0).coeff 556 := by
  rw [G_mul_coeff_ge S0 556 (by norm_num), coeff_sub, X613_coeff_zero 556 (by norm_num),
    T1_coeff_zero 556 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_544, S0_coeff_545, S0_coeff_546, S0_coeff_547, S0_coeff_548, S0_coeff_549, S0_coeff_550, S0_coeff_551, S0_coeff_552, S0_coeff_553, S0_coeff_554, S0_coeff_555, S0_coeff_556]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_557 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 557 = (G * S0).coeff 557 := by
  rw [G_mul_coeff_ge S0 557 (by norm_num), coeff_sub, X613_coeff_zero 557 (by norm_num),
    T1_coeff_zero 557 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_545, S0_coeff_546, S0_coeff_547, S0_coeff_548, S0_coeff_549, S0_coeff_550, S0_coeff_551, S0_coeff_552, S0_coeff_553, S0_coeff_554, S0_coeff_555, S0_coeff_556, S0_coeff_557]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_558 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 558 = (G * S0).coeff 558 := by
  rw [G_mul_coeff_ge S0 558 (by norm_num), coeff_sub, X613_coeff_zero 558 (by norm_num),
    T1_coeff_zero 558 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_546, S0_coeff_547, S0_coeff_548, S0_coeff_549, S0_coeff_550, S0_coeff_551, S0_coeff_552, S0_coeff_553, S0_coeff_554, S0_coeff_555, S0_coeff_556, S0_coeff_557, S0_coeff_558]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_559 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 559 = (G * S0).coeff 559 := by
  rw [G_mul_coeff_ge S0 559 (by norm_num), coeff_sub, X613_coeff_zero 559 (by norm_num),
    T1_coeff_zero 559 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_547, S0_coeff_548, S0_coeff_549, S0_coeff_550, S0_coeff_551, S0_coeff_552, S0_coeff_553, S0_coeff_554, S0_coeff_555, S0_coeff_556, S0_coeff_557, S0_coeff_558, S0_coeff_559]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

lemma chain1_coeff_560 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 560 = (G * S0).coeff 560 := by
  rw [G_mul_coeff_ge S0 560 (by norm_num), coeff_sub, X613_coeff_zero 560 (by norm_num),
    T1_coeff_zero 560 (by norm_num), zero_sub, neg_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_548, S0_coeff_549, S0_coeff_550, S0_coeff_551, S0_coeff_552, S0_coeff_553, S0_coeff_554, S0_coeff_555, S0_coeff_556, S0_coeff_557, S0_coeff_558, S0_coeff_559, S0_coeff_560]
  rw [G_coeff_12, G_coeff_11, G_coeff_10, G_coeff_9, G_coeff_8, G_coeff_7, G_coeff_6, G_coeff_5, G_coeff_4, G_coeff_3, G_coeff_2, G_coeff_1, G_coeff_0]
  decide

/-! ## Range form -/

lemma chain1_coeff_mid (n : ℕ) (hn : 481 ≤ n) (hn' : n ≤ 560) :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff n = (G * S0).coeff n := by
  interval_cases n
  · exact chain1_coeff_481
  · exact chain1_coeff_482
  · exact chain1_coeff_483
  · exact chain1_coeff_484
  · exact chain1_coeff_485
  · exact chain1_coeff_486
  · exact chain1_coeff_487
  · exact chain1_coeff_488
  · exact chain1_coeff_489
  · exact chain1_coeff_490
  · exact chain1_coeff_491
  · exact chain1_coeff_492
  · exact chain1_coeff_493
  · exact chain1_coeff_494
  · exact chain1_coeff_495
  · exact chain1_coeff_496
  · exact chain1_coeff_497
  · exact chain1_coeff_498
  · exact chain1_coeff_499
  · exact chain1_coeff_500
  · exact chain1_coeff_501
  · exact chain1_coeff_502
  · exact chain1_coeff_503
  · exact chain1_coeff_504
  · exact chain1_coeff_505
  · exact chain1_coeff_506
  · exact chain1_coeff_507
  · exact chain1_coeff_508
  · exact chain1_coeff_509
  · exact chain1_coeff_510
  · exact chain1_coeff_511
  · exact chain1_coeff_512
  · exact chain1_coeff_513
  · exact chain1_coeff_514
  · exact chain1_coeff_515
  · exact chain1_coeff_516
  · exact chain1_coeff_517
  · exact chain1_coeff_518
  · exact chain1_coeff_519
  · exact chain1_coeff_520
  · exact chain1_coeff_521
  · exact chain1_coeff_522
  · exact chain1_coeff_523
  · exact chain1_coeff_524
  · exact chain1_coeff_525
  · exact chain1_coeff_526
  · exact chain1_coeff_527
  · exact chain1_coeff_528
  · exact chain1_coeff_529
  · exact chain1_coeff_530
  · exact chain1_coeff_531
  · exact chain1_coeff_532
  · exact chain1_coeff_533
  · exact chain1_coeff_534
  · exact chain1_coeff_535
  · exact chain1_coeff_536
  · exact chain1_coeff_537
  · exact chain1_coeff_538
  · exact chain1_coeff_539
  · exact chain1_coeff_540
  · exact chain1_coeff_541
  · exact chain1_coeff_542
  · exact chain1_coeff_543
  · exact chain1_coeff_544
  · exact chain1_coeff_545
  · exact chain1_coeff_546
  · exact chain1_coeff_547
  · exact chain1_coeff_548
  · exact chain1_coeff_549
  · exact chain1_coeff_550
  · exact chain1_coeff_551
  · exact chain1_coeff_552
  · exact chain1_coeff_553
  · exact chain1_coeff_554
  · exact chain1_coeff_555
  · exact chain1_coeff_556
  · exact chain1_coeff_557
  · exact chain1_coeff_558
  · exact chain1_coeff_559
  · exact chain1_coeff_560

end LeanFormal.IUT.XiFPaper.S2564Chain1Mid7Actual

end
