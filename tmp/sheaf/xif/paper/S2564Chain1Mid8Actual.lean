import tmp.sheaf.xif.paper.S2560S0ShiftedPartsActual
import tmp.sheaf.xif.paper.S2554Mod613ChainDataActual
import tmp.sheaf.xif.paper.S2562GmulCoeffActual
import tmp.sheaf.xif.paper.S2563R6LookupActual
import tmp.sheaf.xif.paper.S2563R7LookupActual

/-!
# Chain-1 coefficient identity, middle range n in [561, 613]

For every n in [561, 613] this file proves
  ((X : (ZMod 613)[X]) ^ 613 - T1).coeff n = (G * S0).coeff n.

Since n < 613 kills the X ^ 613 coefficient and deg T1 = 11, the left side is
zero except at n = 613, where it is 1.  On the right side we use the 13-term
support formula G_mul_coeff_ge; the required S0.coeff k (549 ≤ k ≤ 613)
lookups come from the eight shifted parts of S0, with the contributing
segments R6 (k ≤ 560) and R7 (561 ≤ k ≤ 601) read off from the R6/R7 coeff
lookup files and the remaining segments killed by degree bounds.
-/

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2564Chain1Mid8Actual

open LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual
open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2562GmulCoeffActual
open LeanFormal.IUT.XiFPaper.S2563R6LookupActual
open LeanFormal.IUT.XiFPaper.S2563R7LookupActual

/-! ## Degree bounds for the eight blocks R0, ..., R7 -/

lemma R0_natDegree_le : S2560S0ShiftedPartsActual.R0.natDegree ≤ 80 := by
  unfold S2560S0ShiftedPartsActual.R0; compute_degree!
lemma R1_natDegree_le : S2560S0ShiftedPartsActual.R1.natDegree ≤ 79 := by
  unfold S2560S0ShiftedPartsActual.R1; compute_degree!
lemma R2_natDegree_le : S2560S0ShiftedPartsActual.R2.natDegree ≤ 79 := by
  unfold S2560S0ShiftedPartsActual.R2; compute_degree!
lemma R3_natDegree_le : S2560S0ShiftedPartsActual.R3.natDegree ≤ 79 := by
  unfold S2560S0ShiftedPartsActual.R3; compute_degree!
lemma R4_natDegree_le : S2560S0ShiftedPartsActual.R4.natDegree ≤ 79 := by
  unfold S2560S0ShiftedPartsActual.R4; compute_degree!
lemma R5_natDegree_le : S2560S0ShiftedPartsActual.R5.natDegree ≤ 79 := by
  unfold S2560S0ShiftedPartsActual.R5; compute_degree!
lemma R6_natDegree_le : S2560S0ShiftedPartsActual.R6.natDegree ≤ 79 := by
  unfold S2560S0ShiftedPartsActual.R6; compute_degree!
lemma R7_natDegree_le : S2560S0ShiftedPartsActual.R7.natDegree ≤ 40 := by
  unfold S2560S0ShiftedPartsActual.R7; compute_degree!

lemma coeff_zero_of_natDegree_le {P : (ZMod 613)[X]} {d m : ℕ} (hd : P.natDegree ≤ d) (hm : d < m) :
    P.coeff m = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

lemma R0_coeff_eq_zero_of_gt (m : ℕ) (hm : 80 < m) :
    S2560S0ShiftedPartsActual.R0.coeff m = 0 :=
  coeff_zero_of_natDegree_le R0_natDegree_le hm
lemma R1_coeff_eq_zero_of_gt (m : ℕ) (hm : 79 < m) :
    S2560S0ShiftedPartsActual.R1.coeff m = 0 :=
  coeff_zero_of_natDegree_le R1_natDegree_le hm
lemma R2_coeff_eq_zero_of_gt (m : ℕ) (hm : 79 < m) :
    S2560S0ShiftedPartsActual.R2.coeff m = 0 :=
  coeff_zero_of_natDegree_le R2_natDegree_le hm
lemma R3_coeff_eq_zero_of_gt (m : ℕ) (hm : 79 < m) :
    S2560S0ShiftedPartsActual.R3.coeff m = 0 :=
  coeff_zero_of_natDegree_le R3_natDegree_le hm
lemma R4_coeff_eq_zero_of_gt (m : ℕ) (hm : 79 < m) :
    S2560S0ShiftedPartsActual.R4.coeff m = 0 :=
  coeff_zero_of_natDegree_le R4_natDegree_le hm
lemma R5_coeff_eq_zero_of_gt (m : ℕ) (hm : 79 < m) :
    S2560S0ShiftedPartsActual.R5.coeff m = 0 :=
  coeff_zero_of_natDegree_le R5_natDegree_le hm
lemma R6_coeff_eq_zero_of_gt (m : ℕ) (hm : 79 < m) :
    S2560S0ShiftedPartsActual.R6.coeff m = 0 :=
  coeff_zero_of_natDegree_le R6_natDegree_le hm
lemma R7_coeff_eq_zero_of_gt (m : ℕ) (hm : 40 < m) :
    S2560S0ShiftedPartsActual.R7.coeff m = 0 :=
  coeff_zero_of_natDegree_le R7_natDegree_le hm

/-! ## S0.coeff lookups on 549 ≤ k ≤ 613

S0 = S0_0 + ... + S0_7 with S0_i = X ^ s_i * R_i.  Below 561 only the
sixth block (shift 481) is still alive, from 561 to 601 only the seventh
block (shift 561), and above 601 everything is beyond the supports. -/

lemma S0_coeff_549_560 (k : ℕ) (hk1 : 549 ≤ k) (hk2 : k ≤ 560) :
    S0.coeff k = S2560S0ShiftedPartsActual.R6.coeff (k - 481) := by
  have h0 : S0_0.coeff k = 0 := by
    rw [S0_0_coeff, if_pos (by omega : (0 : ℕ) ≤ k), Nat.sub_zero]
    exact R0_coeff_eq_zero_of_gt k (by omega)
  have h1 : S0_1.coeff k = 0 := by
    rw [S0_1_coeff, if_pos (by omega : (81 : ℕ) ≤ k)]
    exact R1_coeff_eq_zero_of_gt (k - 81) (by omega)
  have h2 : S0_2.coeff k = 0 := by
    rw [S0_2_coeff, if_pos (by omega : (161 : ℕ) ≤ k)]
    exact R2_coeff_eq_zero_of_gt (k - 161) (by omega)
  have h3 : S0_3.coeff k = 0 := by
    rw [S0_3_coeff, if_pos (by omega : (241 : ℕ) ≤ k)]
    exact R3_coeff_eq_zero_of_gt (k - 241) (by omega)
  have h4 : S0_4.coeff k = 0 := by
    rw [S0_4_coeff, if_pos (by omega : (321 : ℕ) ≤ k)]
    exact R4_coeff_eq_zero_of_gt (k - 321) (by omega)
  have h5 : S0_5.coeff k = 0 := by
    rw [S0_5_coeff, if_pos (by omega : (401 : ℕ) ≤ k)]
    exact R5_coeff_eq_zero_of_gt (k - 401) (by omega)
  have h6 : S0_6.coeff k = S2560S0ShiftedPartsActual.R6.coeff (k - 481) := by
    rw [S0_6_coeff, if_pos (by omega : (481 : ℕ) ≤ k)]
  have h7 : S0_7.coeff k = 0 := by
    rw [S0_7_coeff, if_neg (by omega : ¬ (561 : ℕ) ≤ k)]
  rw [S0]
  simp only [Polynomial.coeff_add, h0, h1, h2, h3, h4, h5, h6, h7, zero_add, add_zero]

lemma S0_coeff_561_601 (k : ℕ) (hk1 : 561 ≤ k) (hk2 : k ≤ 601) :
    S0.coeff k = S2560S0ShiftedPartsActual.R7.coeff (k - 561) := by
  have h0 : S0_0.coeff k = 0 := by
    rw [S0_0_coeff, if_pos (by omega : (0 : ℕ) ≤ k), Nat.sub_zero]
    exact R0_coeff_eq_zero_of_gt k (by omega)
  have h1 : S0_1.coeff k = 0 := by
    rw [S0_1_coeff, if_pos (by omega : (81 : ℕ) ≤ k)]
    exact R1_coeff_eq_zero_of_gt (k - 81) (by omega)
  have h2 : S0_2.coeff k = 0 := by
    rw [S0_2_coeff, if_pos (by omega : (161 : ℕ) ≤ k)]
    exact R2_coeff_eq_zero_of_gt (k - 161) (by omega)
  have h3 : S0_3.coeff k = 0 := by
    rw [S0_3_coeff, if_pos (by omega : (241 : ℕ) ≤ k)]
    exact R3_coeff_eq_zero_of_gt (k - 241) (by omega)
  have h4 : S0_4.coeff k = 0 := by
    rw [S0_4_coeff, if_pos (by omega : (321 : ℕ) ≤ k)]
    exact R4_coeff_eq_zero_of_gt (k - 321) (by omega)
  have h5 : S0_5.coeff k = 0 := by
    rw [S0_5_coeff, if_pos (by omega : (401 : ℕ) ≤ k)]
    exact R5_coeff_eq_zero_of_gt (k - 401) (by omega)
  have h6 : S0_6.coeff k = 0 := by
    rw [S0_6_coeff, if_pos (by omega : (481 : ℕ) ≤ k)]
    exact R6_coeff_eq_zero_of_gt (k - 481) (by omega)
  have h7 : S0_7.coeff k = S2560S0ShiftedPartsActual.R7.coeff (k - 561) := by
    rw [S0_7_coeff, if_pos (by omega : (561 : ℕ) ≤ k)]
  rw [S0]
  simp only [Polynomial.coeff_add, h0, h1, h2, h3, h4, h5, h6, h7, zero_add, add_zero]

lemma S0_coeff_602_613 (k : ℕ) (hk1 : 602 ≤ k) (hk2 : k ≤ 613) :
    S0.coeff k = 0 := by
  have h0 : S0_0.coeff k = 0 := by
    rw [S0_0_coeff, if_pos (by omega : (0 : ℕ) ≤ k), Nat.sub_zero]
    exact R0_coeff_eq_zero_of_gt k (by omega)
  have h1 : S0_1.coeff k = 0 := by
    rw [S0_1_coeff, if_pos (by omega : (81 : ℕ) ≤ k)]
    exact R1_coeff_eq_zero_of_gt (k - 81) (by omega)
  have h2 : S0_2.coeff k = 0 := by
    rw [S0_2_coeff, if_pos (by omega : (161 : ℕ) ≤ k)]
    exact R2_coeff_eq_zero_of_gt (k - 161) (by omega)
  have h3 : S0_3.coeff k = 0 := by
    rw [S0_3_coeff, if_pos (by omega : (241 : ℕ) ≤ k)]
    exact R3_coeff_eq_zero_of_gt (k - 241) (by omega)
  have h4 : S0_4.coeff k = 0 := by
    rw [S0_4_coeff, if_pos (by omega : (321 : ℕ) ≤ k)]
    exact R4_coeff_eq_zero_of_gt (k - 321) (by omega)
  have h5 : S0_5.coeff k = 0 := by
    rw [S0_5_coeff, if_pos (by omega : (401 : ℕ) ≤ k)]
    exact R5_coeff_eq_zero_of_gt (k - 401) (by omega)
  have h6 : S0_6.coeff k = 0 := by
    rw [S0_6_coeff, if_pos (by omega : (481 : ℕ) ≤ k)]
    exact R6_coeff_eq_zero_of_gt (k - 481) (by omega)
  have h7 : S0_7.coeff k = 0 := by
    rw [S0_7_coeff, if_pos (by omega : (561 : ℕ) ≤ k)]
    exact R7_coeff_eq_zero_of_gt (k - 561) (by omega)
  rw [S0]
  simp only [Polynomial.coeff_add, h0, h1, h2, h3, h4, h5, h6, h7, add_zero]

lemma S0_coeff_549 : S0.coeff 549 = 277 := by
  rw [S0_coeff_549_560 549 (by norm_num) (by norm_num)]
  exact R6_coeff_68

lemma S0_coeff_550 : S0.coeff 550 = 499 := by
  rw [S0_coeff_549_560 550 (by norm_num) (by norm_num)]
  exact R6_coeff_69

lemma S0_coeff_551 : S0.coeff 551 = 445 := by
  rw [S0_coeff_549_560 551 (by norm_num) (by norm_num)]
  exact R6_coeff_70

lemma S0_coeff_552 : S0.coeff 552 = 297 := by
  rw [S0_coeff_549_560 552 (by norm_num) (by norm_num)]
  exact R6_coeff_71

lemma S0_coeff_553 : S0.coeff 553 = 281 := by
  rw [S0_coeff_549_560 553 (by norm_num) (by norm_num)]
  exact R6_coeff_72

lemma S0_coeff_554 : S0.coeff 554 = 378 := by
  rw [S0_coeff_549_560 554 (by norm_num) (by norm_num)]
  exact R6_coeff_73

lemma S0_coeff_555 : S0.coeff 555 = 417 := by
  rw [S0_coeff_549_560 555 (by norm_num) (by norm_num)]
  exact R6_coeff_74

lemma S0_coeff_556 : S0.coeff 556 = 168 := by
  rw [S0_coeff_549_560 556 (by norm_num) (by norm_num)]
  exact R6_coeff_75

lemma S0_coeff_557 : S0.coeff 557 = 591 := by
  rw [S0_coeff_549_560 557 (by norm_num) (by norm_num)]
  exact R6_coeff_76

lemma S0_coeff_558 : S0.coeff 558 = 56 := by
  rw [S0_coeff_549_560 558 (by norm_num) (by norm_num)]
  exact R6_coeff_77

lemma S0_coeff_559 : S0.coeff 559 = 227 := by
  rw [S0_coeff_549_560 559 (by norm_num) (by norm_num)]
  exact R6_coeff_78

lemma S0_coeff_560 : S0.coeff 560 = 272 := by
  rw [S0_coeff_549_560 560 (by norm_num) (by norm_num)]
  exact R6_coeff_79

lemma S0_coeff_561 : S0.coeff 561 = 456 := by
  rw [S0_coeff_561_601 561 (by norm_num) (by norm_num)]
  exact R7_coeff_0

lemma S0_coeff_562 : S0.coeff 562 = 591 := by
  rw [S0_coeff_561_601 562 (by norm_num) (by norm_num)]
  exact R7_coeff_1

lemma S0_coeff_563 : S0.coeff 563 = 426 := by
  rw [S0_coeff_561_601 563 (by norm_num) (by norm_num)]
  exact R7_coeff_2

lemma S0_coeff_564 : S0.coeff 564 = 254 := by
  rw [S0_coeff_561_601 564 (by norm_num) (by norm_num)]
  exact R7_coeff_3

lemma S0_coeff_565 : S0.coeff 565 = 276 := by
  rw [S0_coeff_561_601 565 (by norm_num) (by norm_num)]
  exact R7_coeff_4

lemma S0_coeff_566 : S0.coeff 566 = 43 := by
  rw [S0_coeff_561_601 566 (by norm_num) (by norm_num)]
  exact R7_coeff_5

lemma S0_coeff_567 : S0.coeff 567 = 190 := by
  rw [S0_coeff_561_601 567 (by norm_num) (by norm_num)]
  exact R7_coeff_6

lemma S0_coeff_568 : S0.coeff 568 = 417 := by
  rw [S0_coeff_561_601 568 (by norm_num) (by norm_num)]
  exact R7_coeff_7

lemma S0_coeff_569 : S0.coeff 569 = 590 := by
  rw [S0_coeff_561_601 569 (by norm_num) (by norm_num)]
  exact R7_coeff_8

lemma S0_coeff_570 : S0.coeff 570 = 124 := by
  rw [S0_coeff_561_601 570 (by norm_num) (by norm_num)]
  exact R7_coeff_9

lemma S0_coeff_571 : S0.coeff 571 = 325 := by
  rw [S0_coeff_561_601 571 (by norm_num) (by norm_num)]
  exact R7_coeff_10

lemma S0_coeff_572 : S0.coeff 572 = 549 := by
  rw [S0_coeff_561_601 572 (by norm_num) (by norm_num)]
  exact R7_coeff_11

lemma S0_coeff_573 : S0.coeff 573 = 60 := by
  rw [S0_coeff_561_601 573 (by norm_num) (by norm_num)]
  exact R7_coeff_12

lemma S0_coeff_574 : S0.coeff 574 = 559 := by
  rw [S0_coeff_561_601 574 (by norm_num) (by norm_num)]
  exact R7_coeff_13

lemma S0_coeff_575 : S0.coeff 575 = 329 := by
  rw [S0_coeff_561_601 575 (by norm_num) (by norm_num)]
  exact R7_coeff_14

lemma S0_coeff_576 : S0.coeff 576 = 366 := by
  rw [S0_coeff_561_601 576 (by norm_num) (by norm_num)]
  exact R7_coeff_15

lemma S0_coeff_577 : S0.coeff 577 = 414 := by
  rw [S0_coeff_561_601 577 (by norm_num) (by norm_num)]
  exact R7_coeff_16

lemma S0_coeff_578 : S0.coeff 578 = 19 := by
  rw [S0_coeff_561_601 578 (by norm_num) (by norm_num)]
  exact R7_coeff_17

lemma S0_coeff_579 : S0.coeff 579 = 75 := by
  rw [S0_coeff_561_601 579 (by norm_num) (by norm_num)]
  exact R7_coeff_18

lemma S0_coeff_580 : S0.coeff 580 = 281 := by
  rw [S0_coeff_561_601 580 (by norm_num) (by norm_num)]
  exact R7_coeff_19

lemma S0_coeff_581 : S0.coeff 581 = 554 := by
  rw [S0_coeff_561_601 581 (by norm_num) (by norm_num)]
  exact R7_coeff_20

lemma S0_coeff_582 : S0.coeff 582 = 540 := by
  rw [S0_coeff_561_601 582 (by norm_num) (by norm_num)]
  exact R7_coeff_21

lemma S0_coeff_583 : S0.coeff 583 = 367 := by
  rw [S0_coeff_561_601 583 (by norm_num) (by norm_num)]
  exact R7_coeff_22

lemma S0_coeff_584 : S0.coeff 584 = 380 := by
  rw [S0_coeff_561_601 584 (by norm_num) (by norm_num)]
  exact R7_coeff_23

lemma S0_coeff_585 : S0.coeff 585 = 510 := by
  rw [S0_coeff_561_601 585 (by norm_num) (by norm_num)]
  exact R7_coeff_24

lemma S0_coeff_586 : S0.coeff 586 = 494 := by
  rw [S0_coeff_561_601 586 (by norm_num) (by norm_num)]
  exact R7_coeff_25

lemma S0_coeff_587 : S0.coeff 587 = 606 := by
  rw [S0_coeff_561_601 587 (by norm_num) (by norm_num)]
  exact R7_coeff_26

lemma S0_coeff_588 : S0.coeff 588 = 509 := by
  rw [S0_coeff_561_601 588 (by norm_num) (by norm_num)]
  exact R7_coeff_27

lemma S0_coeff_589 : S0.coeff 589 = 540 := by
  rw [S0_coeff_561_601 589 (by norm_num) (by norm_num)]
  exact R7_coeff_28

lemma S0_coeff_590 : S0.coeff 590 = 349 := by
  rw [S0_coeff_561_601 590 (by norm_num) (by norm_num)]
  exact R7_coeff_29

lemma S0_coeff_591 : S0.coeff 591 = 74 := by
  rw [S0_coeff_561_601 591 (by norm_num) (by norm_num)]
  exact R7_coeff_30

lemma S0_coeff_592 : S0.coeff 592 = 345 := by
  rw [S0_coeff_561_601 592 (by norm_num) (by norm_num)]
  exact R7_coeff_31

lemma S0_coeff_593 : S0.coeff 593 = 395 := by
  rw [S0_coeff_561_601 593 (by norm_num) (by norm_num)]
  exact R7_coeff_32

lemma S0_coeff_594 : S0.coeff 594 = 161 := by
  rw [S0_coeff_561_601 594 (by norm_num) (by norm_num)]
  exact R7_coeff_33

lemma S0_coeff_595 : S0.coeff 595 = 475 := by
  rw [S0_coeff_561_601 595 (by norm_num) (by norm_num)]
  exact R7_coeff_34

lemma S0_coeff_596 : S0.coeff 596 = 171 := by
  rw [S0_coeff_561_601 596 (by norm_num) (by norm_num)]
  exact R7_coeff_35

lemma S0_coeff_597 : S0.coeff 597 = 459 := by
  rw [S0_coeff_561_601 597 (by norm_num) (by norm_num)]
  exact R7_coeff_36

lemma S0_coeff_598 : S0.coeff 598 = 424 := by
  rw [S0_coeff_561_601 598 (by norm_num) (by norm_num)]
  exact R7_coeff_37

lemma S0_coeff_599 : S0.coeff 599 = 214 := by
  rw [S0_coeff_561_601 599 (by norm_num) (by norm_num)]
  exact R7_coeff_38

lemma S0_coeff_600 : S0.coeff 600 = 341 := by
  rw [S0_coeff_561_601 600 (by norm_num) (by norm_num)]
  exact R7_coeff_39

lemma S0_coeff_601 : S0.coeff 601 = 1 := by
  rw [S0_coeff_561_601 601 (by norm_num) (by norm_num)]
  exact R7_coeff_40

lemma S0_coeff_602 : S0.coeff 602 = 0 :=
  S0_coeff_602_613 602 (by norm_num) (by norm_num)

lemma S0_coeff_603 : S0.coeff 603 = 0 :=
  S0_coeff_602_613 603 (by norm_num) (by norm_num)

lemma S0_coeff_604 : S0.coeff 604 = 0 :=
  S0_coeff_602_613 604 (by norm_num) (by norm_num)

lemma S0_coeff_605 : S0.coeff 605 = 0 :=
  S0_coeff_602_613 605 (by norm_num) (by norm_num)

lemma S0_coeff_606 : S0.coeff 606 = 0 :=
  S0_coeff_602_613 606 (by norm_num) (by norm_num)

lemma S0_coeff_607 : S0.coeff 607 = 0 :=
  S0_coeff_602_613 607 (by norm_num) (by norm_num)

lemma S0_coeff_608 : S0.coeff 608 = 0 :=
  S0_coeff_602_613 608 (by norm_num) (by norm_num)

lemma S0_coeff_609 : S0.coeff 609 = 0 :=
  S0_coeff_602_613 609 (by norm_num) (by norm_num)

lemma S0_coeff_610 : S0.coeff 610 = 0 :=
  S0_coeff_602_613 610 (by norm_num) (by norm_num)

lemma S0_coeff_611 : S0.coeff 611 = 0 :=
  S0_coeff_602_613 611 (by norm_num) (by norm_num)

lemma S0_coeff_612 : S0.coeff 612 = 0 :=
  S0_coeff_602_613 612 (by norm_num) (by norm_num)

lemma S0_coeff_613 : S0.coeff 613 = 0 :=
  S0_coeff_602_613 613 (by norm_num) (by norm_num)

/-! ## The 53 coefficients of the middle range -/

lemma chain1_coeff_561 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 561 = (G * S0).coeff 561 := by
  rw [G_mul_coeff_ge S0 561 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_561, S0_coeff_560, S0_coeff_559, S0_coeff_558, S0_coeff_557, S0_coeff_556, S0_coeff_555, S0_coeff_554, S0_coeff_553, S0_coeff_552, S0_coeff_551, S0_coeff_550, S0_coeff_549]
  simp [G, T1]
  try decide

lemma chain1_coeff_562 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 562 = (G * S0).coeff 562 := by
  rw [G_mul_coeff_ge S0 562 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_562, S0_coeff_561, S0_coeff_560, S0_coeff_559, S0_coeff_558, S0_coeff_557, S0_coeff_556, S0_coeff_555, S0_coeff_554, S0_coeff_553, S0_coeff_552, S0_coeff_551, S0_coeff_550]
  simp [G, T1]
  try decide

lemma chain1_coeff_563 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 563 = (G * S0).coeff 563 := by
  rw [G_mul_coeff_ge S0 563 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_563, S0_coeff_562, S0_coeff_561, S0_coeff_560, S0_coeff_559, S0_coeff_558, S0_coeff_557, S0_coeff_556, S0_coeff_555, S0_coeff_554, S0_coeff_553, S0_coeff_552, S0_coeff_551]
  simp [G, T1]
  try decide

lemma chain1_coeff_564 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 564 = (G * S0).coeff 564 := by
  rw [G_mul_coeff_ge S0 564 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_564, S0_coeff_563, S0_coeff_562, S0_coeff_561, S0_coeff_560, S0_coeff_559, S0_coeff_558, S0_coeff_557, S0_coeff_556, S0_coeff_555, S0_coeff_554, S0_coeff_553, S0_coeff_552]
  simp [G, T1]
  try decide

lemma chain1_coeff_565 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 565 = (G * S0).coeff 565 := by
  rw [G_mul_coeff_ge S0 565 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_565, S0_coeff_564, S0_coeff_563, S0_coeff_562, S0_coeff_561, S0_coeff_560, S0_coeff_559, S0_coeff_558, S0_coeff_557, S0_coeff_556, S0_coeff_555, S0_coeff_554, S0_coeff_553]
  simp [G, T1]
  try decide

lemma chain1_coeff_566 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 566 = (G * S0).coeff 566 := by
  rw [G_mul_coeff_ge S0 566 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_566, S0_coeff_565, S0_coeff_564, S0_coeff_563, S0_coeff_562, S0_coeff_561, S0_coeff_560, S0_coeff_559, S0_coeff_558, S0_coeff_557, S0_coeff_556, S0_coeff_555, S0_coeff_554]
  simp [G, T1]
  try decide

lemma chain1_coeff_567 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 567 = (G * S0).coeff 567 := by
  rw [G_mul_coeff_ge S0 567 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_567, S0_coeff_566, S0_coeff_565, S0_coeff_564, S0_coeff_563, S0_coeff_562, S0_coeff_561, S0_coeff_560, S0_coeff_559, S0_coeff_558, S0_coeff_557, S0_coeff_556, S0_coeff_555]
  simp [G, T1]
  try decide

lemma chain1_coeff_568 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 568 = (G * S0).coeff 568 := by
  rw [G_mul_coeff_ge S0 568 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_568, S0_coeff_567, S0_coeff_566, S0_coeff_565, S0_coeff_564, S0_coeff_563, S0_coeff_562, S0_coeff_561, S0_coeff_560, S0_coeff_559, S0_coeff_558, S0_coeff_557, S0_coeff_556]
  simp [G, T1]
  try decide

lemma chain1_coeff_569 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 569 = (G * S0).coeff 569 := by
  rw [G_mul_coeff_ge S0 569 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_569, S0_coeff_568, S0_coeff_567, S0_coeff_566, S0_coeff_565, S0_coeff_564, S0_coeff_563, S0_coeff_562, S0_coeff_561, S0_coeff_560, S0_coeff_559, S0_coeff_558, S0_coeff_557]
  simp [G, T1]
  try decide

lemma chain1_coeff_570 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 570 = (G * S0).coeff 570 := by
  rw [G_mul_coeff_ge S0 570 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_570, S0_coeff_569, S0_coeff_568, S0_coeff_567, S0_coeff_566, S0_coeff_565, S0_coeff_564, S0_coeff_563, S0_coeff_562, S0_coeff_561, S0_coeff_560, S0_coeff_559, S0_coeff_558]
  simp [G, T1]
  try decide

lemma chain1_coeff_571 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 571 = (G * S0).coeff 571 := by
  rw [G_mul_coeff_ge S0 571 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_571, S0_coeff_570, S0_coeff_569, S0_coeff_568, S0_coeff_567, S0_coeff_566, S0_coeff_565, S0_coeff_564, S0_coeff_563, S0_coeff_562, S0_coeff_561, S0_coeff_560, S0_coeff_559]
  simp [G, T1]
  try decide

lemma chain1_coeff_572 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 572 = (G * S0).coeff 572 := by
  rw [G_mul_coeff_ge S0 572 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_572, S0_coeff_571, S0_coeff_570, S0_coeff_569, S0_coeff_568, S0_coeff_567, S0_coeff_566, S0_coeff_565, S0_coeff_564, S0_coeff_563, S0_coeff_562, S0_coeff_561, S0_coeff_560]
  simp [G, T1]
  try decide

lemma chain1_coeff_573 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 573 = (G * S0).coeff 573 := by
  rw [G_mul_coeff_ge S0 573 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_573, S0_coeff_572, S0_coeff_571, S0_coeff_570, S0_coeff_569, S0_coeff_568, S0_coeff_567, S0_coeff_566, S0_coeff_565, S0_coeff_564, S0_coeff_563, S0_coeff_562, S0_coeff_561]
  simp [G, T1]
  try decide

lemma chain1_coeff_574 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 574 = (G * S0).coeff 574 := by
  rw [G_mul_coeff_ge S0 574 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_574, S0_coeff_573, S0_coeff_572, S0_coeff_571, S0_coeff_570, S0_coeff_569, S0_coeff_568, S0_coeff_567, S0_coeff_566, S0_coeff_565, S0_coeff_564, S0_coeff_563, S0_coeff_562]
  simp [G, T1]
  try decide

lemma chain1_coeff_575 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 575 = (G * S0).coeff 575 := by
  rw [G_mul_coeff_ge S0 575 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_575, S0_coeff_574, S0_coeff_573, S0_coeff_572, S0_coeff_571, S0_coeff_570, S0_coeff_569, S0_coeff_568, S0_coeff_567, S0_coeff_566, S0_coeff_565, S0_coeff_564, S0_coeff_563]
  simp [G, T1]
  try decide

lemma chain1_coeff_576 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 576 = (G * S0).coeff 576 := by
  rw [G_mul_coeff_ge S0 576 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_576, S0_coeff_575, S0_coeff_574, S0_coeff_573, S0_coeff_572, S0_coeff_571, S0_coeff_570, S0_coeff_569, S0_coeff_568, S0_coeff_567, S0_coeff_566, S0_coeff_565, S0_coeff_564]
  simp [G, T1]
  try decide

lemma chain1_coeff_577 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 577 = (G * S0).coeff 577 := by
  rw [G_mul_coeff_ge S0 577 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_577, S0_coeff_576, S0_coeff_575, S0_coeff_574, S0_coeff_573, S0_coeff_572, S0_coeff_571, S0_coeff_570, S0_coeff_569, S0_coeff_568, S0_coeff_567, S0_coeff_566, S0_coeff_565]
  simp [G, T1]
  try decide

lemma chain1_coeff_578 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 578 = (G * S0).coeff 578 := by
  rw [G_mul_coeff_ge S0 578 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_578, S0_coeff_577, S0_coeff_576, S0_coeff_575, S0_coeff_574, S0_coeff_573, S0_coeff_572, S0_coeff_571, S0_coeff_570, S0_coeff_569, S0_coeff_568, S0_coeff_567, S0_coeff_566]
  simp [G, T1]
  try decide

lemma chain1_coeff_579 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 579 = (G * S0).coeff 579 := by
  rw [G_mul_coeff_ge S0 579 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_579, S0_coeff_578, S0_coeff_577, S0_coeff_576, S0_coeff_575, S0_coeff_574, S0_coeff_573, S0_coeff_572, S0_coeff_571, S0_coeff_570, S0_coeff_569, S0_coeff_568, S0_coeff_567]
  simp [G, T1]
  try decide

lemma chain1_coeff_580 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 580 = (G * S0).coeff 580 := by
  rw [G_mul_coeff_ge S0 580 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_580, S0_coeff_579, S0_coeff_578, S0_coeff_577, S0_coeff_576, S0_coeff_575, S0_coeff_574, S0_coeff_573, S0_coeff_572, S0_coeff_571, S0_coeff_570, S0_coeff_569, S0_coeff_568]
  simp [G, T1]
  try decide

lemma chain1_coeff_581 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 581 = (G * S0).coeff 581 := by
  rw [G_mul_coeff_ge S0 581 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_581, S0_coeff_580, S0_coeff_579, S0_coeff_578, S0_coeff_577, S0_coeff_576, S0_coeff_575, S0_coeff_574, S0_coeff_573, S0_coeff_572, S0_coeff_571, S0_coeff_570, S0_coeff_569]
  simp [G, T1]
  try decide

lemma chain1_coeff_582 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 582 = (G * S0).coeff 582 := by
  rw [G_mul_coeff_ge S0 582 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_582, S0_coeff_581, S0_coeff_580, S0_coeff_579, S0_coeff_578, S0_coeff_577, S0_coeff_576, S0_coeff_575, S0_coeff_574, S0_coeff_573, S0_coeff_572, S0_coeff_571, S0_coeff_570]
  simp [G, T1]
  try decide

lemma chain1_coeff_583 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 583 = (G * S0).coeff 583 := by
  rw [G_mul_coeff_ge S0 583 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_583, S0_coeff_582, S0_coeff_581, S0_coeff_580, S0_coeff_579, S0_coeff_578, S0_coeff_577, S0_coeff_576, S0_coeff_575, S0_coeff_574, S0_coeff_573, S0_coeff_572, S0_coeff_571]
  simp [G, T1]
  try decide

lemma chain1_coeff_584 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 584 = (G * S0).coeff 584 := by
  rw [G_mul_coeff_ge S0 584 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_584, S0_coeff_583, S0_coeff_582, S0_coeff_581, S0_coeff_580, S0_coeff_579, S0_coeff_578, S0_coeff_577, S0_coeff_576, S0_coeff_575, S0_coeff_574, S0_coeff_573, S0_coeff_572]
  simp [G, T1]
  try decide

lemma chain1_coeff_585 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 585 = (G * S0).coeff 585 := by
  rw [G_mul_coeff_ge S0 585 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_585, S0_coeff_584, S0_coeff_583, S0_coeff_582, S0_coeff_581, S0_coeff_580, S0_coeff_579, S0_coeff_578, S0_coeff_577, S0_coeff_576, S0_coeff_575, S0_coeff_574, S0_coeff_573]
  simp [G, T1]
  try decide

lemma chain1_coeff_586 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 586 = (G * S0).coeff 586 := by
  rw [G_mul_coeff_ge S0 586 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_586, S0_coeff_585, S0_coeff_584, S0_coeff_583, S0_coeff_582, S0_coeff_581, S0_coeff_580, S0_coeff_579, S0_coeff_578, S0_coeff_577, S0_coeff_576, S0_coeff_575, S0_coeff_574]
  simp [G, T1]
  try decide

lemma chain1_coeff_587 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 587 = (G * S0).coeff 587 := by
  rw [G_mul_coeff_ge S0 587 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_587, S0_coeff_586, S0_coeff_585, S0_coeff_584, S0_coeff_583, S0_coeff_582, S0_coeff_581, S0_coeff_580, S0_coeff_579, S0_coeff_578, S0_coeff_577, S0_coeff_576, S0_coeff_575]
  simp [G, T1]
  try decide

lemma chain1_coeff_588 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 588 = (G * S0).coeff 588 := by
  rw [G_mul_coeff_ge S0 588 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_588, S0_coeff_587, S0_coeff_586, S0_coeff_585, S0_coeff_584, S0_coeff_583, S0_coeff_582, S0_coeff_581, S0_coeff_580, S0_coeff_579, S0_coeff_578, S0_coeff_577, S0_coeff_576]
  simp [G, T1]
  try decide

lemma chain1_coeff_589 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 589 = (G * S0).coeff 589 := by
  rw [G_mul_coeff_ge S0 589 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_589, S0_coeff_588, S0_coeff_587, S0_coeff_586, S0_coeff_585, S0_coeff_584, S0_coeff_583, S0_coeff_582, S0_coeff_581, S0_coeff_580, S0_coeff_579, S0_coeff_578, S0_coeff_577]
  simp [G, T1]
  try decide

lemma chain1_coeff_590 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 590 = (G * S0).coeff 590 := by
  rw [G_mul_coeff_ge S0 590 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_590, S0_coeff_589, S0_coeff_588, S0_coeff_587, S0_coeff_586, S0_coeff_585, S0_coeff_584, S0_coeff_583, S0_coeff_582, S0_coeff_581, S0_coeff_580, S0_coeff_579, S0_coeff_578]
  simp [G, T1]
  try decide

lemma chain1_coeff_591 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 591 = (G * S0).coeff 591 := by
  rw [G_mul_coeff_ge S0 591 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_591, S0_coeff_590, S0_coeff_589, S0_coeff_588, S0_coeff_587, S0_coeff_586, S0_coeff_585, S0_coeff_584, S0_coeff_583, S0_coeff_582, S0_coeff_581, S0_coeff_580, S0_coeff_579]
  simp [G, T1]
  try decide

lemma chain1_coeff_592 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 592 = (G * S0).coeff 592 := by
  rw [G_mul_coeff_ge S0 592 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_592, S0_coeff_591, S0_coeff_590, S0_coeff_589, S0_coeff_588, S0_coeff_587, S0_coeff_586, S0_coeff_585, S0_coeff_584, S0_coeff_583, S0_coeff_582, S0_coeff_581, S0_coeff_580]
  simp [G, T1]
  try decide

lemma chain1_coeff_593 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 593 = (G * S0).coeff 593 := by
  rw [G_mul_coeff_ge S0 593 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_593, S0_coeff_592, S0_coeff_591, S0_coeff_590, S0_coeff_589, S0_coeff_588, S0_coeff_587, S0_coeff_586, S0_coeff_585, S0_coeff_584, S0_coeff_583, S0_coeff_582, S0_coeff_581]
  simp [G, T1]
  try decide

lemma chain1_coeff_594 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 594 = (G * S0).coeff 594 := by
  rw [G_mul_coeff_ge S0 594 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_594, S0_coeff_593, S0_coeff_592, S0_coeff_591, S0_coeff_590, S0_coeff_589, S0_coeff_588, S0_coeff_587, S0_coeff_586, S0_coeff_585, S0_coeff_584, S0_coeff_583, S0_coeff_582]
  simp [G, T1]
  try decide

lemma chain1_coeff_595 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 595 = (G * S0).coeff 595 := by
  rw [G_mul_coeff_ge S0 595 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_595, S0_coeff_594, S0_coeff_593, S0_coeff_592, S0_coeff_591, S0_coeff_590, S0_coeff_589, S0_coeff_588, S0_coeff_587, S0_coeff_586, S0_coeff_585, S0_coeff_584, S0_coeff_583]
  simp [G, T1]
  try decide

lemma chain1_coeff_596 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 596 = (G * S0).coeff 596 := by
  rw [G_mul_coeff_ge S0 596 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_596, S0_coeff_595, S0_coeff_594, S0_coeff_593, S0_coeff_592, S0_coeff_591, S0_coeff_590, S0_coeff_589, S0_coeff_588, S0_coeff_587, S0_coeff_586, S0_coeff_585, S0_coeff_584]
  simp [G, T1]
  try decide

lemma chain1_coeff_597 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 597 = (G * S0).coeff 597 := by
  rw [G_mul_coeff_ge S0 597 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_597, S0_coeff_596, S0_coeff_595, S0_coeff_594, S0_coeff_593, S0_coeff_592, S0_coeff_591, S0_coeff_590, S0_coeff_589, S0_coeff_588, S0_coeff_587, S0_coeff_586, S0_coeff_585]
  simp [G, T1]
  try decide

lemma chain1_coeff_598 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 598 = (G * S0).coeff 598 := by
  rw [G_mul_coeff_ge S0 598 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_598, S0_coeff_597, S0_coeff_596, S0_coeff_595, S0_coeff_594, S0_coeff_593, S0_coeff_592, S0_coeff_591, S0_coeff_590, S0_coeff_589, S0_coeff_588, S0_coeff_587, S0_coeff_586]
  simp [G, T1]
  try decide

lemma chain1_coeff_599 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 599 = (G * S0).coeff 599 := by
  rw [G_mul_coeff_ge S0 599 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_599, S0_coeff_598, S0_coeff_597, S0_coeff_596, S0_coeff_595, S0_coeff_594, S0_coeff_593, S0_coeff_592, S0_coeff_591, S0_coeff_590, S0_coeff_589, S0_coeff_588, S0_coeff_587]
  simp [G, T1]
  try decide

lemma chain1_coeff_600 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 600 = (G * S0).coeff 600 := by
  rw [G_mul_coeff_ge S0 600 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_600, S0_coeff_599, S0_coeff_598, S0_coeff_597, S0_coeff_596, S0_coeff_595, S0_coeff_594, S0_coeff_593, S0_coeff_592, S0_coeff_591, S0_coeff_590, S0_coeff_589, S0_coeff_588]
  simp [G, T1]
  try decide

lemma chain1_coeff_601 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 601 = (G * S0).coeff 601 := by
  rw [G_mul_coeff_ge S0 601 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_601, S0_coeff_600, S0_coeff_599, S0_coeff_598, S0_coeff_597, S0_coeff_596, S0_coeff_595, S0_coeff_594, S0_coeff_593, S0_coeff_592, S0_coeff_591, S0_coeff_590, S0_coeff_589]
  simp [G, T1]
  try decide

lemma chain1_coeff_602 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 602 = (G * S0).coeff 602 := by
  rw [G_mul_coeff_ge S0 602 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_602, S0_coeff_601, S0_coeff_600, S0_coeff_599, S0_coeff_598, S0_coeff_597, S0_coeff_596, S0_coeff_595, S0_coeff_594, S0_coeff_593, S0_coeff_592, S0_coeff_591, S0_coeff_590]
  simp [G, T1]
  try decide

lemma chain1_coeff_603 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 603 = (G * S0).coeff 603 := by
  rw [G_mul_coeff_ge S0 603 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_603, S0_coeff_602, S0_coeff_601, S0_coeff_600, S0_coeff_599, S0_coeff_598, S0_coeff_597, S0_coeff_596, S0_coeff_595, S0_coeff_594, S0_coeff_593, S0_coeff_592, S0_coeff_591]
  simp [G, T1]
  try decide

lemma chain1_coeff_604 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 604 = (G * S0).coeff 604 := by
  rw [G_mul_coeff_ge S0 604 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_604, S0_coeff_603, S0_coeff_602, S0_coeff_601, S0_coeff_600, S0_coeff_599, S0_coeff_598, S0_coeff_597, S0_coeff_596, S0_coeff_595, S0_coeff_594, S0_coeff_593, S0_coeff_592]
  simp [G, T1]
  try decide

lemma chain1_coeff_605 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 605 = (G * S0).coeff 605 := by
  rw [G_mul_coeff_ge S0 605 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_605, S0_coeff_604, S0_coeff_603, S0_coeff_602, S0_coeff_601, S0_coeff_600, S0_coeff_599, S0_coeff_598, S0_coeff_597, S0_coeff_596, S0_coeff_595, S0_coeff_594, S0_coeff_593]
  simp [G, T1]
  try decide

lemma chain1_coeff_606 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 606 = (G * S0).coeff 606 := by
  rw [G_mul_coeff_ge S0 606 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_606, S0_coeff_605, S0_coeff_604, S0_coeff_603, S0_coeff_602, S0_coeff_601, S0_coeff_600, S0_coeff_599, S0_coeff_598, S0_coeff_597, S0_coeff_596, S0_coeff_595, S0_coeff_594]
  simp [G, T1]
  try decide

lemma chain1_coeff_607 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 607 = (G * S0).coeff 607 := by
  rw [G_mul_coeff_ge S0 607 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_607, S0_coeff_606, S0_coeff_605, S0_coeff_604, S0_coeff_603, S0_coeff_602, S0_coeff_601, S0_coeff_600, S0_coeff_599, S0_coeff_598, S0_coeff_597, S0_coeff_596, S0_coeff_595]
  simp [G, T1]
  try decide

lemma chain1_coeff_608 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 608 = (G * S0).coeff 608 := by
  rw [G_mul_coeff_ge S0 608 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_608, S0_coeff_607, S0_coeff_606, S0_coeff_605, S0_coeff_604, S0_coeff_603, S0_coeff_602, S0_coeff_601, S0_coeff_600, S0_coeff_599, S0_coeff_598, S0_coeff_597, S0_coeff_596]
  simp [G, T1]
  try decide

lemma chain1_coeff_609 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 609 = (G * S0).coeff 609 := by
  rw [G_mul_coeff_ge S0 609 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_609, S0_coeff_608, S0_coeff_607, S0_coeff_606, S0_coeff_605, S0_coeff_604, S0_coeff_603, S0_coeff_602, S0_coeff_601, S0_coeff_600, S0_coeff_599, S0_coeff_598, S0_coeff_597]
  simp [G, T1]
  try decide

lemma chain1_coeff_610 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 610 = (G * S0).coeff 610 := by
  rw [G_mul_coeff_ge S0 610 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_610, S0_coeff_609, S0_coeff_608, S0_coeff_607, S0_coeff_606, S0_coeff_605, S0_coeff_604, S0_coeff_603, S0_coeff_602, S0_coeff_601, S0_coeff_600, S0_coeff_599, S0_coeff_598]
  simp [G, T1]
  try decide

lemma chain1_coeff_611 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 611 = (G * S0).coeff 611 := by
  rw [G_mul_coeff_ge S0 611 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_611, S0_coeff_610, S0_coeff_609, S0_coeff_608, S0_coeff_607, S0_coeff_606, S0_coeff_605, S0_coeff_604, S0_coeff_603, S0_coeff_602, S0_coeff_601, S0_coeff_600, S0_coeff_599]
  simp [G, T1]
  try decide

lemma chain1_coeff_612 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 612 = (G * S0).coeff 612 := by
  rw [G_mul_coeff_ge S0 612 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_612, S0_coeff_611, S0_coeff_610, S0_coeff_609, S0_coeff_608, S0_coeff_607, S0_coeff_606, S0_coeff_605, S0_coeff_604, S0_coeff_603, S0_coeff_602, S0_coeff_601, S0_coeff_600]
  simp [G, T1]
  try decide

lemma chain1_coeff_613 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 613 = (G * S0).coeff 613 := by
  rw [G_mul_coeff_ge S0 613 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_613, S0_coeff_612, S0_coeff_611, S0_coeff_610, S0_coeff_609, S0_coeff_608, S0_coeff_607, S0_coeff_606, S0_coeff_605, S0_coeff_604, S0_coeff_603, S0_coeff_602, S0_coeff_601]
  simp [G, T1]
  try decide

theorem chain1_coeff_mid (n : ℕ) (hn1 : 561 ≤ n) (hn2 : n ≤ 613) :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff n = (G * S0).coeff n := by
  interval_cases n <;>
    simp only [chain1_coeff_561, chain1_coeff_562, chain1_coeff_563, chain1_coeff_564, chain1_coeff_565, chain1_coeff_566, chain1_coeff_567, chain1_coeff_568, chain1_coeff_569, chain1_coeff_570, chain1_coeff_571, chain1_coeff_572, chain1_coeff_573, chain1_coeff_574, chain1_coeff_575, chain1_coeff_576, chain1_coeff_577, chain1_coeff_578, chain1_coeff_579, chain1_coeff_580, chain1_coeff_581, chain1_coeff_582, chain1_coeff_583, chain1_coeff_584, chain1_coeff_585, chain1_coeff_586, chain1_coeff_587, chain1_coeff_588, chain1_coeff_589, chain1_coeff_590, chain1_coeff_591, chain1_coeff_592, chain1_coeff_593, chain1_coeff_594, chain1_coeff_595, chain1_coeff_596, chain1_coeff_597, chain1_coeff_598, chain1_coeff_599, chain1_coeff_600, chain1_coeff_601, chain1_coeff_602, chain1_coeff_603, chain1_coeff_604, chain1_coeff_605, chain1_coeff_606, chain1_coeff_607, chain1_coeff_608, chain1_coeff_609, chain1_coeff_610, chain1_coeff_611, chain1_coeff_612, chain1_coeff_613]

end LeanFormal.IUT.XiFPaper.S2564Chain1Mid8Actual

end
