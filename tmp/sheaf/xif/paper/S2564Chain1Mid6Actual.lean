/-
S2564 chain 1: actual coefficients in degrees 401..480 (sixth block).

Target, for every n in [401, 480]:
  ((X : (ZMod 613)[X]) ^ 613 - T1).coeff n = (G * S0).coeff n

Since deg T1 <= 11 and n < 613, the left-hand side is -T1.coeff n = 0
(lemma lhs_coeff_eq_zero). The right-hand side is expanded into its
13-term support sum (G_mul_coeff_ge), and each S0.coeff k with
389 <= k <= 480 is looked up through the eight shifted pieces S0_i
(lemmas S0_coeff_389 .. S0_coeff_480). Only two pieces contribute on
this window:
* 389 <= k <= 400: only S0_4 = X^321 * R4 is active, value R4.coeff (k-321);
* 401 <= k <= 480: only S0_5 = X^401 * R5 is active, value R5.coeff (k-401).
Every other piece vanishes, either because k is below its shift or because
it is above the degree bound of its block (R0: 80, R1..R4: 79). These two
window reductions are the lemmas S0_coeff_389_400 and S0_coeff_401_480.
The resulting numeric identity in ZMod 613 is closed by decide in each
per-degree lemma chain1_coeff_401 .. chain1_coeff_480, and
chain1_mid6 repackages those 80 lemmas as one quantified statement.

Dependencies (all actual, no axioms added):
* S2560S0ShiftedPartsActual: R0..R7, S0_i, S0, S0_i_coeff;
* S2554Mod613ChainDataActual: G, T1;
* S2562GmulCoeffActual: G_mul_coeff_ge;
* S2563R4LookupActual: R4_coeff_68 .. R4_coeff_79;
* S2563R5LookupActual: R5_coeff_0 .. R5_coeff_79.

Note on names: the repository also contains root-level R0..R5 over ZMod 29,
so every reference to the mod-613 blocks is written with its full name
S2560S0ShiftedPartsActual.Ri.

Verification: lake env lean -j1 -R D:\lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S2564Chain1Mid6Actual.olean
tmp/sheaf/xif/paper/S2564Chain1Mid6Actual.lean  (EXIT 0, no warnings; no sorry,
no native_decide, no extra axiom).
-/

import tmp.sheaf.xif.paper.S2560S0ShiftedPartsActual
import tmp.sheaf.xif.paper.S2554Mod613ChainDataActual
import tmp.sheaf.xif.paper.S2562GmulCoeffActual
import tmp.sheaf.xif.paper.S2563R4LookupActual
import tmp.sheaf.xif.paper.S2563R5LookupActual

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2564Chain1Mid6Actual

open LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual
open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2562GmulCoeffActual
open LeanFormal.IUT.XiFPaper.S2563R4LookupActual
open LeanFormal.IUT.XiFPaper.S2563R5LookupActual

/-- The five low blocks of S0 have degree bounds. -/
lemma R0_natDegree_le : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.natDegree ≤ 80 := by unfold LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0; compute_degree!

lemma R1_natDegree_le : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.natDegree ≤ 79 := by unfold LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1; compute_degree!

lemma R2_natDegree_le : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R2.natDegree ≤ 79 := by unfold LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R2; compute_degree!

lemma R3_natDegree_le : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R3.natDegree ≤ 79 := by unfold LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R3; compute_degree!

lemma R4_natDegree_le : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R4.natDegree ≤ 79 := by unfold LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R4; compute_degree!

lemma R0_coeff_eq_zero_of_gt (m : ℕ) (hm : 80 < m) : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff m = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have h := R0_natDegree_le
  omega

lemma R1_coeff_eq_zero_of_gt (m : ℕ) (hm : 79 < m) : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff m = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have h := R1_natDegree_le
  omega

lemma R2_coeff_eq_zero_of_gt (m : ℕ) (hm : 79 < m) : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R2.coeff m = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have h := R2_natDegree_le
  omega

lemma R3_coeff_eq_zero_of_gt (m : ℕ) (hm : 79 < m) : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R3.coeff m = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have h := R3_natDegree_le
  omega

lemma R4_coeff_eq_zero_of_gt (m : ℕ) (hm : 79 < m) : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R4.coeff m = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have h := R4_natDegree_le
  omega

/-- On the window [389,400] only the fifth block of S0 contributes. -/
lemma S0_coeff_389_400 (k : ℕ) (hk1 : 389 ≤ k) (hk2 : k ≤ 400) :
    S0.coeff k = LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R4.coeff (k - 321) := by
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
  have h4 : S0_4.coeff k =
      LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R4.coeff (k - 321) := by
    rw [S0_4_coeff, if_pos (by omega : (321 : ℕ) ≤ k)]
  have h5 : S0_5.coeff k = 0 := by
    rw [S0_5_coeff, if_neg (by omega : ¬ (401 : ℕ) ≤ k)]
  have h6 : S0_6.coeff k = 0 := by
    rw [S0_6_coeff, if_neg (by omega : ¬ (481 : ℕ) ≤ k)]
  have h7 : S0_7.coeff k = 0 := by
    rw [S0_7_coeff, if_neg (by omega : ¬ (561 : ℕ) ≤ k)]
  rw [S0]
  simp only [Polynomial.coeff_add, h0, h1, h2, h3, h4, h5, h6, h7, zero_add, add_zero]

/-- On the window [401,480] only the sixth block of S0 contributes. -/
lemma S0_coeff_401_480 (k : ℕ) (hk1 : 401 ≤ k) (hk2 : k ≤ 480) :
    S0.coeff k = LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R5.coeff (k - 401) := by
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
  have h5 : S0_5.coeff k =
      LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R5.coeff (k - 401) := by
    rw [S0_5_coeff, if_pos (by omega : (401 : ℕ) ≤ k)]
  have h6 : S0_6.coeff k = 0 := by
    rw [S0_6_coeff, if_neg (by omega : ¬ (481 : ℕ) ≤ k)]
  have h7 : S0_7.coeff k = 0 := by
    rw [S0_7_coeff, if_neg (by omega : ¬ (561 : ℕ) ≤ k)]
  rw [S0]
  simp only [Polynomial.coeff_add, h0, h1, h2, h3, h4, h5, h6, h7, zero_add, add_zero]

/-- The low-degree target polynomial T1 vanishes from degree 12 on. -/
lemma T1_natDegree_le : T1.natDegree ≤ 11 := by unfold T1; compute_degree!

lemma T1_coeff_eq_zero (m : ℕ) (hm : 12 ≤ m) : T1.coeff m = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have h := T1_natDegree_le
  omega

/-- For degrees below 613 the left hand side is minus the T1 coefficient, hence zero. -/
lemma lhs_coeff_eq_zero (n : ℕ) (hn1 : 12 ≤ n) (hn2 : n < 613) :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff n = 0 := by
  rw [Polynomial.coeff_sub, T1_coeff_eq_zero n hn1, Polynomial.coeff_X_pow]
  simp only [if_neg (by omega : ¬ n = (613 : ℕ)), sub_zero]

/-- The thirteen coefficients of the monic normalization G. -/

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

/-! ## S0 coefficient lookup on [389,480] -/

lemma S0_coeff_389 : S0.coeff 389 = 448 := by
  rw [S0_coeff_389_400 389 (by norm_num) (by norm_num)]
  norm_num
  exact R4_coeff_68

lemma S0_coeff_390 : S0.coeff 390 = 47 := by
  rw [S0_coeff_389_400 390 (by norm_num) (by norm_num)]
  norm_num
  exact R4_coeff_69

lemma S0_coeff_391 : S0.coeff 391 = 7 := by
  rw [S0_coeff_389_400 391 (by norm_num) (by norm_num)]
  norm_num
  exact R4_coeff_70

lemma S0_coeff_392 : S0.coeff 392 = 597 := by
  rw [S0_coeff_389_400 392 (by norm_num) (by norm_num)]
  norm_num
  exact R4_coeff_71

lemma S0_coeff_393 : S0.coeff 393 = 75 := by
  rw [S0_coeff_389_400 393 (by norm_num) (by norm_num)]
  norm_num
  exact R4_coeff_72

lemma S0_coeff_394 : S0.coeff 394 = 47 := by
  rw [S0_coeff_389_400 394 (by norm_num) (by norm_num)]
  norm_num
  exact R4_coeff_73

lemma S0_coeff_395 : S0.coeff 395 = 204 := by
  rw [S0_coeff_389_400 395 (by norm_num) (by norm_num)]
  norm_num
  exact R4_coeff_74

lemma S0_coeff_396 : S0.coeff 396 = 285 := by
  rw [S0_coeff_389_400 396 (by norm_num) (by norm_num)]
  norm_num
  exact R4_coeff_75

lemma S0_coeff_397 : S0.coeff 397 = 241 := by
  rw [S0_coeff_389_400 397 (by norm_num) (by norm_num)]
  norm_num
  exact R4_coeff_76

lemma S0_coeff_398 : S0.coeff 398 = 60 := by
  rw [S0_coeff_389_400 398 (by norm_num) (by norm_num)]
  norm_num
  exact R4_coeff_77

lemma S0_coeff_399 : S0.coeff 399 = 597 := by
  rw [S0_coeff_389_400 399 (by norm_num) (by norm_num)]
  norm_num
  exact R4_coeff_78

lemma S0_coeff_400 : S0.coeff 400 = 320 := by
  rw [S0_coeff_389_400 400 (by norm_num) (by norm_num)]
  norm_num
  exact R4_coeff_79

lemma S0_coeff_401 : S0.coeff 401 = 329 := by
  rw [S0_coeff_401_480 401 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_0

lemma S0_coeff_402 : S0.coeff 402 = 248 := by
  rw [S0_coeff_401_480 402 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_1

lemma S0_coeff_403 : S0.coeff 403 = 185 := by
  rw [S0_coeff_401_480 403 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_2

lemma S0_coeff_404 : S0.coeff 404 = 308 := by
  rw [S0_coeff_401_480 404 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_3

lemma S0_coeff_405 : S0.coeff 405 = 233 := by
  rw [S0_coeff_401_480 405 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_4

lemma S0_coeff_406 : S0.coeff 406 = 120 := by
  rw [S0_coeff_401_480 406 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_5

lemma S0_coeff_407 : S0.coeff 407 = 112 := by
  rw [S0_coeff_401_480 407 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_6

lemma S0_coeff_408 : S0.coeff 408 = 137 := by
  rw [S0_coeff_401_480 408 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_7

lemma S0_coeff_409 : S0.coeff 409 = 567 := by
  rw [S0_coeff_401_480 409 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_8

lemma S0_coeff_410 : S0.coeff 410 = 473 := by
  rw [S0_coeff_401_480 410 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_9

lemma S0_coeff_411 : S0.coeff 411 = 579 := by
  rw [S0_coeff_401_480 411 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_10

lemma S0_coeff_412 : S0.coeff 412 = 18 := by
  rw [S0_coeff_401_480 412 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_11

lemma S0_coeff_413 : S0.coeff 413 = 527 := by
  rw [S0_coeff_401_480 413 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_12

lemma S0_coeff_414 : S0.coeff 414 = 351 := by
  rw [S0_coeff_401_480 414 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_13

lemma S0_coeff_415 : S0.coeff 415 = 53 := by
  rw [S0_coeff_401_480 415 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_14

lemma S0_coeff_416 : S0.coeff 416 = 47 := by
  rw [S0_coeff_401_480 416 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_15

lemma S0_coeff_417 : S0.coeff 417 = 388 := by
  rw [S0_coeff_401_480 417 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_16

lemma S0_coeff_418 : S0.coeff 418 = 507 := by
  rw [S0_coeff_401_480 418 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_17

lemma S0_coeff_419 : S0.coeff 419 = 441 := by
  rw [S0_coeff_401_480 419 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_18

lemma S0_coeff_420 : S0.coeff 420 = 473 := by
  rw [S0_coeff_401_480 420 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_19

lemma S0_coeff_421 : S0.coeff 421 = 348 := by
  rw [S0_coeff_401_480 421 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_20

lemma S0_coeff_422 : S0.coeff 422 = 18 := by
  rw [S0_coeff_401_480 422 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_21

lemma S0_coeff_423 : S0.coeff 423 = 296 := by
  rw [S0_coeff_401_480 423 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_22

lemma S0_coeff_424 : S0.coeff 424 = 131 := by
  rw [S0_coeff_401_480 424 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_23

lemma S0_coeff_425 : S0.coeff 425 = 560 := by
  rw [S0_coeff_401_480 425 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_24

lemma S0_coeff_426 : S0.coeff 426 = 11 := by
  rw [S0_coeff_401_480 426 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_25

lemma S0_coeff_427 : S0.coeff 427 = 314 := by
  rw [S0_coeff_401_480 427 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_26

lemma S0_coeff_428 : S0.coeff 428 = 386 := by
  rw [S0_coeff_401_480 428 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_27

lemma S0_coeff_429 : S0.coeff 429 = 258 := by
  rw [S0_coeff_401_480 429 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_28

lemma S0_coeff_430 : S0.coeff 430 = 376 := by
  rw [S0_coeff_401_480 430 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_29

lemma S0_coeff_431 : S0.coeff 431 = 284 := by
  rw [S0_coeff_401_480 431 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_30

lemma S0_coeff_432 : S0.coeff 432 = 481 := by
  rw [S0_coeff_401_480 432 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_31

lemma S0_coeff_433 : S0.coeff 433 = 325 := by
  rw [S0_coeff_401_480 433 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_32

lemma S0_coeff_434 : S0.coeff 434 = 336 := by
  rw [S0_coeff_401_480 434 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_33

lemma S0_coeff_435 : S0.coeff 435 = 469 := by
  rw [S0_coeff_401_480 435 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_34

lemma S0_coeff_436 : S0.coeff 436 = 59 := by
  rw [S0_coeff_401_480 436 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_35

lemma S0_coeff_437 : S0.coeff 437 = 165 := by
  rw [S0_coeff_401_480 437 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_36

lemma S0_coeff_438 : S0.coeff 438 = 234 := by
  rw [S0_coeff_401_480 438 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_37

lemma S0_coeff_439 : S0.coeff 439 = 477 := by
  rw [S0_coeff_401_480 439 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_38

lemma S0_coeff_440 : S0.coeff 440 = 599 := by
  rw [S0_coeff_401_480 440 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_39

lemma S0_coeff_441 : S0.coeff 441 = 179 := by
  rw [S0_coeff_401_480 441 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_40

lemma S0_coeff_442 : S0.coeff 442 = 372 := by
  rw [S0_coeff_401_480 442 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_41

lemma S0_coeff_443 : S0.coeff 443 = 308 := by
  rw [S0_coeff_401_480 443 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_42

lemma S0_coeff_444 : S0.coeff 444 = 180 := by
  rw [S0_coeff_401_480 444 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_43

lemma S0_coeff_445 : S0.coeff 445 = 101 := by
  rw [S0_coeff_401_480 445 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_44

lemma S0_coeff_446 : S0.coeff 446 = 437 := by
  rw [S0_coeff_401_480 446 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_45

lemma S0_coeff_447 : S0.coeff 447 = 176 := by
  rw [S0_coeff_401_480 447 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_46

lemma S0_coeff_448 : S0.coeff 448 = 282 := by
  rw [S0_coeff_401_480 448 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_47

lemma S0_coeff_449 : S0.coeff 449 = 280 := by
  rw [S0_coeff_401_480 449 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_48

lemma S0_coeff_450 : S0.coeff 450 = 182 := by
  rw [S0_coeff_401_480 450 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_49

lemma S0_coeff_451 : S0.coeff 451 = 455 := by
  rw [S0_coeff_401_480 451 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_50

lemma S0_coeff_452 : S0.coeff 452 = 504 := by
  rw [S0_coeff_401_480 452 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_51

lemma S0_coeff_453 : S0.coeff 453 = 127 := by
  rw [S0_coeff_401_480 453 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_52

lemma S0_coeff_454 : S0.coeff 454 = 332 := by
  rw [S0_coeff_401_480 454 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_53

lemma S0_coeff_455 : S0.coeff 455 = 337 := by
  rw [S0_coeff_401_480 455 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_54

lemma S0_coeff_456 : S0.coeff 456 = 518 := by
  rw [S0_coeff_401_480 456 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_55

lemma S0_coeff_457 : S0.coeff 457 = 241 := by
  rw [S0_coeff_401_480 457 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_56

lemma S0_coeff_458 : S0.coeff 458 = 507 := by
  rw [S0_coeff_401_480 458 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_57

lemma S0_coeff_459 : S0.coeff 459 = 483 := by
  rw [S0_coeff_401_480 459 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_58

lemma S0_coeff_460 : S0.coeff 460 = 308 := by
  rw [S0_coeff_401_480 460 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_59

lemma S0_coeff_461 : S0.coeff 461 = 155 := by
  rw [S0_coeff_401_480 461 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_60

lemma S0_coeff_462 : S0.coeff 462 = 450 := by
  rw [S0_coeff_401_480 462 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_61

lemma S0_coeff_463 : S0.coeff 463 = 76 := by
  rw [S0_coeff_401_480 463 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_62

lemma S0_coeff_464 : S0.coeff 464 = 529 := by
  rw [S0_coeff_401_480 464 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_63

lemma S0_coeff_465 : S0.coeff 465 = 251 := by
  rw [S0_coeff_401_480 465 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_64

lemma S0_coeff_466 : S0.coeff 466 = 320 := by
  rw [S0_coeff_401_480 466 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_65

lemma S0_coeff_467 : S0.coeff 467 = 449 := by
  rw [S0_coeff_401_480 467 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_66

lemma S0_coeff_468 : S0.coeff 468 = 376 := by
  rw [S0_coeff_401_480 468 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_67

lemma S0_coeff_469 : S0.coeff 469 = 187 := by
  rw [S0_coeff_401_480 469 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_68

lemma S0_coeff_470 : S0.coeff 470 = 262 := by
  rw [S0_coeff_401_480 470 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_69

lemma S0_coeff_471 : S0.coeff 471 = 202 := by
  rw [S0_coeff_401_480 471 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_70

lemma S0_coeff_472 : S0.coeff 472 = 408 := by
  rw [S0_coeff_401_480 472 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_71

lemma S0_coeff_473 : S0.coeff 473 = 469 := by
  rw [S0_coeff_401_480 473 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_72

lemma S0_coeff_474 : S0.coeff 474 = 210 := by
  rw [S0_coeff_401_480 474 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_73

lemma S0_coeff_475 : S0.coeff 475 = 306 := by
  rw [S0_coeff_401_480 475 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_74

lemma S0_coeff_476 : S0.coeff 476 = 172 := by
  rw [S0_coeff_401_480 476 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_75

lemma S0_coeff_477 : S0.coeff 477 = 427 := by
  rw [S0_coeff_401_480 477 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_76

lemma S0_coeff_478 : S0.coeff 478 = 261 := by
  rw [S0_coeff_401_480 478 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_77

lemma S0_coeff_479 : S0.coeff 479 = 482 := by
  rw [S0_coeff_401_480 479 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_78

lemma S0_coeff_480 : S0.coeff 480 = 172 := by
  rw [S0_coeff_401_480 480 (by norm_num) (by norm_num)]
  norm_num
  exact R5_coeff_79

/-! ## Chain 1 coefficients on [401,480] -/

lemma chain1_coeff_401 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 401 = (G * S0).coeff 401 := by
  rw [G_mul_coeff_ge S0 401 (by norm_num), lhs_coeff_eq_zero 401 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_401, S0_coeff_400, S0_coeff_399, S0_coeff_398, S0_coeff_397, S0_coeff_396, S0_coeff_395, S0_coeff_394, S0_coeff_393, S0_coeff_392, S0_coeff_391, S0_coeff_390, S0_coeff_389, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_402 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 402 = (G * S0).coeff 402 := by
  rw [G_mul_coeff_ge S0 402 (by norm_num), lhs_coeff_eq_zero 402 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_402, S0_coeff_401, S0_coeff_400, S0_coeff_399, S0_coeff_398, S0_coeff_397, S0_coeff_396, S0_coeff_395, S0_coeff_394, S0_coeff_393, S0_coeff_392, S0_coeff_391, S0_coeff_390, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_403 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 403 = (G * S0).coeff 403 := by
  rw [G_mul_coeff_ge S0 403 (by norm_num), lhs_coeff_eq_zero 403 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_403, S0_coeff_402, S0_coeff_401, S0_coeff_400, S0_coeff_399, S0_coeff_398, S0_coeff_397, S0_coeff_396, S0_coeff_395, S0_coeff_394, S0_coeff_393, S0_coeff_392, S0_coeff_391, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_404 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 404 = (G * S0).coeff 404 := by
  rw [G_mul_coeff_ge S0 404 (by norm_num), lhs_coeff_eq_zero 404 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_404, S0_coeff_403, S0_coeff_402, S0_coeff_401, S0_coeff_400, S0_coeff_399, S0_coeff_398, S0_coeff_397, S0_coeff_396, S0_coeff_395, S0_coeff_394, S0_coeff_393, S0_coeff_392, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_405 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 405 = (G * S0).coeff 405 := by
  rw [G_mul_coeff_ge S0 405 (by norm_num), lhs_coeff_eq_zero 405 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_405, S0_coeff_404, S0_coeff_403, S0_coeff_402, S0_coeff_401, S0_coeff_400, S0_coeff_399, S0_coeff_398, S0_coeff_397, S0_coeff_396, S0_coeff_395, S0_coeff_394, S0_coeff_393, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_406 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 406 = (G * S0).coeff 406 := by
  rw [G_mul_coeff_ge S0 406 (by norm_num), lhs_coeff_eq_zero 406 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_406, S0_coeff_405, S0_coeff_404, S0_coeff_403, S0_coeff_402, S0_coeff_401, S0_coeff_400, S0_coeff_399, S0_coeff_398, S0_coeff_397, S0_coeff_396, S0_coeff_395, S0_coeff_394, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_407 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 407 = (G * S0).coeff 407 := by
  rw [G_mul_coeff_ge S0 407 (by norm_num), lhs_coeff_eq_zero 407 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_407, S0_coeff_406, S0_coeff_405, S0_coeff_404, S0_coeff_403, S0_coeff_402, S0_coeff_401, S0_coeff_400, S0_coeff_399, S0_coeff_398, S0_coeff_397, S0_coeff_396, S0_coeff_395, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_408 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 408 = (G * S0).coeff 408 := by
  rw [G_mul_coeff_ge S0 408 (by norm_num), lhs_coeff_eq_zero 408 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_408, S0_coeff_407, S0_coeff_406, S0_coeff_405, S0_coeff_404, S0_coeff_403, S0_coeff_402, S0_coeff_401, S0_coeff_400, S0_coeff_399, S0_coeff_398, S0_coeff_397, S0_coeff_396, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_409 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 409 = (G * S0).coeff 409 := by
  rw [G_mul_coeff_ge S0 409 (by norm_num), lhs_coeff_eq_zero 409 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_409, S0_coeff_408, S0_coeff_407, S0_coeff_406, S0_coeff_405, S0_coeff_404, S0_coeff_403, S0_coeff_402, S0_coeff_401, S0_coeff_400, S0_coeff_399, S0_coeff_398, S0_coeff_397, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_410 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 410 = (G * S0).coeff 410 := by
  rw [G_mul_coeff_ge S0 410 (by norm_num), lhs_coeff_eq_zero 410 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_410, S0_coeff_409, S0_coeff_408, S0_coeff_407, S0_coeff_406, S0_coeff_405, S0_coeff_404, S0_coeff_403, S0_coeff_402, S0_coeff_401, S0_coeff_400, S0_coeff_399, S0_coeff_398, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_411 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 411 = (G * S0).coeff 411 := by
  rw [G_mul_coeff_ge S0 411 (by norm_num), lhs_coeff_eq_zero 411 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_411, S0_coeff_410, S0_coeff_409, S0_coeff_408, S0_coeff_407, S0_coeff_406, S0_coeff_405, S0_coeff_404, S0_coeff_403, S0_coeff_402, S0_coeff_401, S0_coeff_400, S0_coeff_399, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_412 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 412 = (G * S0).coeff 412 := by
  rw [G_mul_coeff_ge S0 412 (by norm_num), lhs_coeff_eq_zero 412 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_412, S0_coeff_411, S0_coeff_410, S0_coeff_409, S0_coeff_408, S0_coeff_407, S0_coeff_406, S0_coeff_405, S0_coeff_404, S0_coeff_403, S0_coeff_402, S0_coeff_401, S0_coeff_400, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_413 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 413 = (G * S0).coeff 413 := by
  rw [G_mul_coeff_ge S0 413 (by norm_num), lhs_coeff_eq_zero 413 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_413, S0_coeff_412, S0_coeff_411, S0_coeff_410, S0_coeff_409, S0_coeff_408, S0_coeff_407, S0_coeff_406, S0_coeff_405, S0_coeff_404, S0_coeff_403, S0_coeff_402, S0_coeff_401, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_414 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 414 = (G * S0).coeff 414 := by
  rw [G_mul_coeff_ge S0 414 (by norm_num), lhs_coeff_eq_zero 414 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_414, S0_coeff_413, S0_coeff_412, S0_coeff_411, S0_coeff_410, S0_coeff_409, S0_coeff_408, S0_coeff_407, S0_coeff_406, S0_coeff_405, S0_coeff_404, S0_coeff_403, S0_coeff_402, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_415 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 415 = (G * S0).coeff 415 := by
  rw [G_mul_coeff_ge S0 415 (by norm_num), lhs_coeff_eq_zero 415 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_415, S0_coeff_414, S0_coeff_413, S0_coeff_412, S0_coeff_411, S0_coeff_410, S0_coeff_409, S0_coeff_408, S0_coeff_407, S0_coeff_406, S0_coeff_405, S0_coeff_404, S0_coeff_403, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_416 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 416 = (G * S0).coeff 416 := by
  rw [G_mul_coeff_ge S0 416 (by norm_num), lhs_coeff_eq_zero 416 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_416, S0_coeff_415, S0_coeff_414, S0_coeff_413, S0_coeff_412, S0_coeff_411, S0_coeff_410, S0_coeff_409, S0_coeff_408, S0_coeff_407, S0_coeff_406, S0_coeff_405, S0_coeff_404, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_417 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 417 = (G * S0).coeff 417 := by
  rw [G_mul_coeff_ge S0 417 (by norm_num), lhs_coeff_eq_zero 417 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_417, S0_coeff_416, S0_coeff_415, S0_coeff_414, S0_coeff_413, S0_coeff_412, S0_coeff_411, S0_coeff_410, S0_coeff_409, S0_coeff_408, S0_coeff_407, S0_coeff_406, S0_coeff_405, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_418 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 418 = (G * S0).coeff 418 := by
  rw [G_mul_coeff_ge S0 418 (by norm_num), lhs_coeff_eq_zero 418 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_418, S0_coeff_417, S0_coeff_416, S0_coeff_415, S0_coeff_414, S0_coeff_413, S0_coeff_412, S0_coeff_411, S0_coeff_410, S0_coeff_409, S0_coeff_408, S0_coeff_407, S0_coeff_406, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_419 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 419 = (G * S0).coeff 419 := by
  rw [G_mul_coeff_ge S0 419 (by norm_num), lhs_coeff_eq_zero 419 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_419, S0_coeff_418, S0_coeff_417, S0_coeff_416, S0_coeff_415, S0_coeff_414, S0_coeff_413, S0_coeff_412, S0_coeff_411, S0_coeff_410, S0_coeff_409, S0_coeff_408, S0_coeff_407, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_420 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 420 = (G * S0).coeff 420 := by
  rw [G_mul_coeff_ge S0 420 (by norm_num), lhs_coeff_eq_zero 420 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_420, S0_coeff_419, S0_coeff_418, S0_coeff_417, S0_coeff_416, S0_coeff_415, S0_coeff_414, S0_coeff_413, S0_coeff_412, S0_coeff_411, S0_coeff_410, S0_coeff_409, S0_coeff_408, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_421 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 421 = (G * S0).coeff 421 := by
  rw [G_mul_coeff_ge S0 421 (by norm_num), lhs_coeff_eq_zero 421 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_421, S0_coeff_420, S0_coeff_419, S0_coeff_418, S0_coeff_417, S0_coeff_416, S0_coeff_415, S0_coeff_414, S0_coeff_413, S0_coeff_412, S0_coeff_411, S0_coeff_410, S0_coeff_409, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_422 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 422 = (G * S0).coeff 422 := by
  rw [G_mul_coeff_ge S0 422 (by norm_num), lhs_coeff_eq_zero 422 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_422, S0_coeff_421, S0_coeff_420, S0_coeff_419, S0_coeff_418, S0_coeff_417, S0_coeff_416, S0_coeff_415, S0_coeff_414, S0_coeff_413, S0_coeff_412, S0_coeff_411, S0_coeff_410, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_423 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 423 = (G * S0).coeff 423 := by
  rw [G_mul_coeff_ge S0 423 (by norm_num), lhs_coeff_eq_zero 423 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_423, S0_coeff_422, S0_coeff_421, S0_coeff_420, S0_coeff_419, S0_coeff_418, S0_coeff_417, S0_coeff_416, S0_coeff_415, S0_coeff_414, S0_coeff_413, S0_coeff_412, S0_coeff_411, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_424 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 424 = (G * S0).coeff 424 := by
  rw [G_mul_coeff_ge S0 424 (by norm_num), lhs_coeff_eq_zero 424 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_424, S0_coeff_423, S0_coeff_422, S0_coeff_421, S0_coeff_420, S0_coeff_419, S0_coeff_418, S0_coeff_417, S0_coeff_416, S0_coeff_415, S0_coeff_414, S0_coeff_413, S0_coeff_412, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_425 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 425 = (G * S0).coeff 425 := by
  rw [G_mul_coeff_ge S0 425 (by norm_num), lhs_coeff_eq_zero 425 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_425, S0_coeff_424, S0_coeff_423, S0_coeff_422, S0_coeff_421, S0_coeff_420, S0_coeff_419, S0_coeff_418, S0_coeff_417, S0_coeff_416, S0_coeff_415, S0_coeff_414, S0_coeff_413, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_426 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 426 = (G * S0).coeff 426 := by
  rw [G_mul_coeff_ge S0 426 (by norm_num), lhs_coeff_eq_zero 426 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_426, S0_coeff_425, S0_coeff_424, S0_coeff_423, S0_coeff_422, S0_coeff_421, S0_coeff_420, S0_coeff_419, S0_coeff_418, S0_coeff_417, S0_coeff_416, S0_coeff_415, S0_coeff_414, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_427 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 427 = (G * S0).coeff 427 := by
  rw [G_mul_coeff_ge S0 427 (by norm_num), lhs_coeff_eq_zero 427 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_427, S0_coeff_426, S0_coeff_425, S0_coeff_424, S0_coeff_423, S0_coeff_422, S0_coeff_421, S0_coeff_420, S0_coeff_419, S0_coeff_418, S0_coeff_417, S0_coeff_416, S0_coeff_415, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_428 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 428 = (G * S0).coeff 428 := by
  rw [G_mul_coeff_ge S0 428 (by norm_num), lhs_coeff_eq_zero 428 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_428, S0_coeff_427, S0_coeff_426, S0_coeff_425, S0_coeff_424, S0_coeff_423, S0_coeff_422, S0_coeff_421, S0_coeff_420, S0_coeff_419, S0_coeff_418, S0_coeff_417, S0_coeff_416, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_429 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 429 = (G * S0).coeff 429 := by
  rw [G_mul_coeff_ge S0 429 (by norm_num), lhs_coeff_eq_zero 429 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_429, S0_coeff_428, S0_coeff_427, S0_coeff_426, S0_coeff_425, S0_coeff_424, S0_coeff_423, S0_coeff_422, S0_coeff_421, S0_coeff_420, S0_coeff_419, S0_coeff_418, S0_coeff_417, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_430 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 430 = (G * S0).coeff 430 := by
  rw [G_mul_coeff_ge S0 430 (by norm_num), lhs_coeff_eq_zero 430 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_430, S0_coeff_429, S0_coeff_428, S0_coeff_427, S0_coeff_426, S0_coeff_425, S0_coeff_424, S0_coeff_423, S0_coeff_422, S0_coeff_421, S0_coeff_420, S0_coeff_419, S0_coeff_418, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_431 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 431 = (G * S0).coeff 431 := by
  rw [G_mul_coeff_ge S0 431 (by norm_num), lhs_coeff_eq_zero 431 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_431, S0_coeff_430, S0_coeff_429, S0_coeff_428, S0_coeff_427, S0_coeff_426, S0_coeff_425, S0_coeff_424, S0_coeff_423, S0_coeff_422, S0_coeff_421, S0_coeff_420, S0_coeff_419, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_432 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 432 = (G * S0).coeff 432 := by
  rw [G_mul_coeff_ge S0 432 (by norm_num), lhs_coeff_eq_zero 432 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_432, S0_coeff_431, S0_coeff_430, S0_coeff_429, S0_coeff_428, S0_coeff_427, S0_coeff_426, S0_coeff_425, S0_coeff_424, S0_coeff_423, S0_coeff_422, S0_coeff_421, S0_coeff_420, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_433 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 433 = (G * S0).coeff 433 := by
  rw [G_mul_coeff_ge S0 433 (by norm_num), lhs_coeff_eq_zero 433 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_433, S0_coeff_432, S0_coeff_431, S0_coeff_430, S0_coeff_429, S0_coeff_428, S0_coeff_427, S0_coeff_426, S0_coeff_425, S0_coeff_424, S0_coeff_423, S0_coeff_422, S0_coeff_421, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_434 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 434 = (G * S0).coeff 434 := by
  rw [G_mul_coeff_ge S0 434 (by norm_num), lhs_coeff_eq_zero 434 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_434, S0_coeff_433, S0_coeff_432, S0_coeff_431, S0_coeff_430, S0_coeff_429, S0_coeff_428, S0_coeff_427, S0_coeff_426, S0_coeff_425, S0_coeff_424, S0_coeff_423, S0_coeff_422, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_435 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 435 = (G * S0).coeff 435 := by
  rw [G_mul_coeff_ge S0 435 (by norm_num), lhs_coeff_eq_zero 435 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_435, S0_coeff_434, S0_coeff_433, S0_coeff_432, S0_coeff_431, S0_coeff_430, S0_coeff_429, S0_coeff_428, S0_coeff_427, S0_coeff_426, S0_coeff_425, S0_coeff_424, S0_coeff_423, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_436 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 436 = (G * S0).coeff 436 := by
  rw [G_mul_coeff_ge S0 436 (by norm_num), lhs_coeff_eq_zero 436 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_436, S0_coeff_435, S0_coeff_434, S0_coeff_433, S0_coeff_432, S0_coeff_431, S0_coeff_430, S0_coeff_429, S0_coeff_428, S0_coeff_427, S0_coeff_426, S0_coeff_425, S0_coeff_424, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_437 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 437 = (G * S0).coeff 437 := by
  rw [G_mul_coeff_ge S0 437 (by norm_num), lhs_coeff_eq_zero 437 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_437, S0_coeff_436, S0_coeff_435, S0_coeff_434, S0_coeff_433, S0_coeff_432, S0_coeff_431, S0_coeff_430, S0_coeff_429, S0_coeff_428, S0_coeff_427, S0_coeff_426, S0_coeff_425, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_438 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 438 = (G * S0).coeff 438 := by
  rw [G_mul_coeff_ge S0 438 (by norm_num), lhs_coeff_eq_zero 438 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_438, S0_coeff_437, S0_coeff_436, S0_coeff_435, S0_coeff_434, S0_coeff_433, S0_coeff_432, S0_coeff_431, S0_coeff_430, S0_coeff_429, S0_coeff_428, S0_coeff_427, S0_coeff_426, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_439 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 439 = (G * S0).coeff 439 := by
  rw [G_mul_coeff_ge S0 439 (by norm_num), lhs_coeff_eq_zero 439 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_439, S0_coeff_438, S0_coeff_437, S0_coeff_436, S0_coeff_435, S0_coeff_434, S0_coeff_433, S0_coeff_432, S0_coeff_431, S0_coeff_430, S0_coeff_429, S0_coeff_428, S0_coeff_427, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_440 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 440 = (G * S0).coeff 440 := by
  rw [G_mul_coeff_ge S0 440 (by norm_num), lhs_coeff_eq_zero 440 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_440, S0_coeff_439, S0_coeff_438, S0_coeff_437, S0_coeff_436, S0_coeff_435, S0_coeff_434, S0_coeff_433, S0_coeff_432, S0_coeff_431, S0_coeff_430, S0_coeff_429, S0_coeff_428, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_441 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 441 = (G * S0).coeff 441 := by
  rw [G_mul_coeff_ge S0 441 (by norm_num), lhs_coeff_eq_zero 441 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_441, S0_coeff_440, S0_coeff_439, S0_coeff_438, S0_coeff_437, S0_coeff_436, S0_coeff_435, S0_coeff_434, S0_coeff_433, S0_coeff_432, S0_coeff_431, S0_coeff_430, S0_coeff_429, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_442 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 442 = (G * S0).coeff 442 := by
  rw [G_mul_coeff_ge S0 442 (by norm_num), lhs_coeff_eq_zero 442 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_442, S0_coeff_441, S0_coeff_440, S0_coeff_439, S0_coeff_438, S0_coeff_437, S0_coeff_436, S0_coeff_435, S0_coeff_434, S0_coeff_433, S0_coeff_432, S0_coeff_431, S0_coeff_430, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_443 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 443 = (G * S0).coeff 443 := by
  rw [G_mul_coeff_ge S0 443 (by norm_num), lhs_coeff_eq_zero 443 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_443, S0_coeff_442, S0_coeff_441, S0_coeff_440, S0_coeff_439, S0_coeff_438, S0_coeff_437, S0_coeff_436, S0_coeff_435, S0_coeff_434, S0_coeff_433, S0_coeff_432, S0_coeff_431, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_444 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 444 = (G * S0).coeff 444 := by
  rw [G_mul_coeff_ge S0 444 (by norm_num), lhs_coeff_eq_zero 444 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_444, S0_coeff_443, S0_coeff_442, S0_coeff_441, S0_coeff_440, S0_coeff_439, S0_coeff_438, S0_coeff_437, S0_coeff_436, S0_coeff_435, S0_coeff_434, S0_coeff_433, S0_coeff_432, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_445 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 445 = (G * S0).coeff 445 := by
  rw [G_mul_coeff_ge S0 445 (by norm_num), lhs_coeff_eq_zero 445 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_445, S0_coeff_444, S0_coeff_443, S0_coeff_442, S0_coeff_441, S0_coeff_440, S0_coeff_439, S0_coeff_438, S0_coeff_437, S0_coeff_436, S0_coeff_435, S0_coeff_434, S0_coeff_433, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_446 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 446 = (G * S0).coeff 446 := by
  rw [G_mul_coeff_ge S0 446 (by norm_num), lhs_coeff_eq_zero 446 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_446, S0_coeff_445, S0_coeff_444, S0_coeff_443, S0_coeff_442, S0_coeff_441, S0_coeff_440, S0_coeff_439, S0_coeff_438, S0_coeff_437, S0_coeff_436, S0_coeff_435, S0_coeff_434, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_447 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 447 = (G * S0).coeff 447 := by
  rw [G_mul_coeff_ge S0 447 (by norm_num), lhs_coeff_eq_zero 447 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_447, S0_coeff_446, S0_coeff_445, S0_coeff_444, S0_coeff_443, S0_coeff_442, S0_coeff_441, S0_coeff_440, S0_coeff_439, S0_coeff_438, S0_coeff_437, S0_coeff_436, S0_coeff_435, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_448 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 448 = (G * S0).coeff 448 := by
  rw [G_mul_coeff_ge S0 448 (by norm_num), lhs_coeff_eq_zero 448 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_448, S0_coeff_447, S0_coeff_446, S0_coeff_445, S0_coeff_444, S0_coeff_443, S0_coeff_442, S0_coeff_441, S0_coeff_440, S0_coeff_439, S0_coeff_438, S0_coeff_437, S0_coeff_436, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_449 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 449 = (G * S0).coeff 449 := by
  rw [G_mul_coeff_ge S0 449 (by norm_num), lhs_coeff_eq_zero 449 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_449, S0_coeff_448, S0_coeff_447, S0_coeff_446, S0_coeff_445, S0_coeff_444, S0_coeff_443, S0_coeff_442, S0_coeff_441, S0_coeff_440, S0_coeff_439, S0_coeff_438, S0_coeff_437, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_450 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 450 = (G * S0).coeff 450 := by
  rw [G_mul_coeff_ge S0 450 (by norm_num), lhs_coeff_eq_zero 450 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_450, S0_coeff_449, S0_coeff_448, S0_coeff_447, S0_coeff_446, S0_coeff_445, S0_coeff_444, S0_coeff_443, S0_coeff_442, S0_coeff_441, S0_coeff_440, S0_coeff_439, S0_coeff_438, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_451 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 451 = (G * S0).coeff 451 := by
  rw [G_mul_coeff_ge S0 451 (by norm_num), lhs_coeff_eq_zero 451 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_451, S0_coeff_450, S0_coeff_449, S0_coeff_448, S0_coeff_447, S0_coeff_446, S0_coeff_445, S0_coeff_444, S0_coeff_443, S0_coeff_442, S0_coeff_441, S0_coeff_440, S0_coeff_439, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_452 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 452 = (G * S0).coeff 452 := by
  rw [G_mul_coeff_ge S0 452 (by norm_num), lhs_coeff_eq_zero 452 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_452, S0_coeff_451, S0_coeff_450, S0_coeff_449, S0_coeff_448, S0_coeff_447, S0_coeff_446, S0_coeff_445, S0_coeff_444, S0_coeff_443, S0_coeff_442, S0_coeff_441, S0_coeff_440, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_453 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 453 = (G * S0).coeff 453 := by
  rw [G_mul_coeff_ge S0 453 (by norm_num), lhs_coeff_eq_zero 453 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_453, S0_coeff_452, S0_coeff_451, S0_coeff_450, S0_coeff_449, S0_coeff_448, S0_coeff_447, S0_coeff_446, S0_coeff_445, S0_coeff_444, S0_coeff_443, S0_coeff_442, S0_coeff_441, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_454 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 454 = (G * S0).coeff 454 := by
  rw [G_mul_coeff_ge S0 454 (by norm_num), lhs_coeff_eq_zero 454 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_454, S0_coeff_453, S0_coeff_452, S0_coeff_451, S0_coeff_450, S0_coeff_449, S0_coeff_448, S0_coeff_447, S0_coeff_446, S0_coeff_445, S0_coeff_444, S0_coeff_443, S0_coeff_442, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_455 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 455 = (G * S0).coeff 455 := by
  rw [G_mul_coeff_ge S0 455 (by norm_num), lhs_coeff_eq_zero 455 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_455, S0_coeff_454, S0_coeff_453, S0_coeff_452, S0_coeff_451, S0_coeff_450, S0_coeff_449, S0_coeff_448, S0_coeff_447, S0_coeff_446, S0_coeff_445, S0_coeff_444, S0_coeff_443, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_456 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 456 = (G * S0).coeff 456 := by
  rw [G_mul_coeff_ge S0 456 (by norm_num), lhs_coeff_eq_zero 456 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_456, S0_coeff_455, S0_coeff_454, S0_coeff_453, S0_coeff_452, S0_coeff_451, S0_coeff_450, S0_coeff_449, S0_coeff_448, S0_coeff_447, S0_coeff_446, S0_coeff_445, S0_coeff_444, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_457 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 457 = (G * S0).coeff 457 := by
  rw [G_mul_coeff_ge S0 457 (by norm_num), lhs_coeff_eq_zero 457 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_457, S0_coeff_456, S0_coeff_455, S0_coeff_454, S0_coeff_453, S0_coeff_452, S0_coeff_451, S0_coeff_450, S0_coeff_449, S0_coeff_448, S0_coeff_447, S0_coeff_446, S0_coeff_445, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_458 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 458 = (G * S0).coeff 458 := by
  rw [G_mul_coeff_ge S0 458 (by norm_num), lhs_coeff_eq_zero 458 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_458, S0_coeff_457, S0_coeff_456, S0_coeff_455, S0_coeff_454, S0_coeff_453, S0_coeff_452, S0_coeff_451, S0_coeff_450, S0_coeff_449, S0_coeff_448, S0_coeff_447, S0_coeff_446, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_459 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 459 = (G * S0).coeff 459 := by
  rw [G_mul_coeff_ge S0 459 (by norm_num), lhs_coeff_eq_zero 459 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_459, S0_coeff_458, S0_coeff_457, S0_coeff_456, S0_coeff_455, S0_coeff_454, S0_coeff_453, S0_coeff_452, S0_coeff_451, S0_coeff_450, S0_coeff_449, S0_coeff_448, S0_coeff_447, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_460 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 460 = (G * S0).coeff 460 := by
  rw [G_mul_coeff_ge S0 460 (by norm_num), lhs_coeff_eq_zero 460 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_460, S0_coeff_459, S0_coeff_458, S0_coeff_457, S0_coeff_456, S0_coeff_455, S0_coeff_454, S0_coeff_453, S0_coeff_452, S0_coeff_451, S0_coeff_450, S0_coeff_449, S0_coeff_448, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_461 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 461 = (G * S0).coeff 461 := by
  rw [G_mul_coeff_ge S0 461 (by norm_num), lhs_coeff_eq_zero 461 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_461, S0_coeff_460, S0_coeff_459, S0_coeff_458, S0_coeff_457, S0_coeff_456, S0_coeff_455, S0_coeff_454, S0_coeff_453, S0_coeff_452, S0_coeff_451, S0_coeff_450, S0_coeff_449, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_462 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 462 = (G * S0).coeff 462 := by
  rw [G_mul_coeff_ge S0 462 (by norm_num), lhs_coeff_eq_zero 462 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_462, S0_coeff_461, S0_coeff_460, S0_coeff_459, S0_coeff_458, S0_coeff_457, S0_coeff_456, S0_coeff_455, S0_coeff_454, S0_coeff_453, S0_coeff_452, S0_coeff_451, S0_coeff_450, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_463 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 463 = (G * S0).coeff 463 := by
  rw [G_mul_coeff_ge S0 463 (by norm_num), lhs_coeff_eq_zero 463 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_463, S0_coeff_462, S0_coeff_461, S0_coeff_460, S0_coeff_459, S0_coeff_458, S0_coeff_457, S0_coeff_456, S0_coeff_455, S0_coeff_454, S0_coeff_453, S0_coeff_452, S0_coeff_451, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_464 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 464 = (G * S0).coeff 464 := by
  rw [G_mul_coeff_ge S0 464 (by norm_num), lhs_coeff_eq_zero 464 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_464, S0_coeff_463, S0_coeff_462, S0_coeff_461, S0_coeff_460, S0_coeff_459, S0_coeff_458, S0_coeff_457, S0_coeff_456, S0_coeff_455, S0_coeff_454, S0_coeff_453, S0_coeff_452, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_465 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 465 = (G * S0).coeff 465 := by
  rw [G_mul_coeff_ge S0 465 (by norm_num), lhs_coeff_eq_zero 465 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_465, S0_coeff_464, S0_coeff_463, S0_coeff_462, S0_coeff_461, S0_coeff_460, S0_coeff_459, S0_coeff_458, S0_coeff_457, S0_coeff_456, S0_coeff_455, S0_coeff_454, S0_coeff_453, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_466 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 466 = (G * S0).coeff 466 := by
  rw [G_mul_coeff_ge S0 466 (by norm_num), lhs_coeff_eq_zero 466 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_466, S0_coeff_465, S0_coeff_464, S0_coeff_463, S0_coeff_462, S0_coeff_461, S0_coeff_460, S0_coeff_459, S0_coeff_458, S0_coeff_457, S0_coeff_456, S0_coeff_455, S0_coeff_454, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_467 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 467 = (G * S0).coeff 467 := by
  rw [G_mul_coeff_ge S0 467 (by norm_num), lhs_coeff_eq_zero 467 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_467, S0_coeff_466, S0_coeff_465, S0_coeff_464, S0_coeff_463, S0_coeff_462, S0_coeff_461, S0_coeff_460, S0_coeff_459, S0_coeff_458, S0_coeff_457, S0_coeff_456, S0_coeff_455, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_468 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 468 = (G * S0).coeff 468 := by
  rw [G_mul_coeff_ge S0 468 (by norm_num), lhs_coeff_eq_zero 468 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_468, S0_coeff_467, S0_coeff_466, S0_coeff_465, S0_coeff_464, S0_coeff_463, S0_coeff_462, S0_coeff_461, S0_coeff_460, S0_coeff_459, S0_coeff_458, S0_coeff_457, S0_coeff_456, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_469 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 469 = (G * S0).coeff 469 := by
  rw [G_mul_coeff_ge S0 469 (by norm_num), lhs_coeff_eq_zero 469 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_469, S0_coeff_468, S0_coeff_467, S0_coeff_466, S0_coeff_465, S0_coeff_464, S0_coeff_463, S0_coeff_462, S0_coeff_461, S0_coeff_460, S0_coeff_459, S0_coeff_458, S0_coeff_457, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_470 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 470 = (G * S0).coeff 470 := by
  rw [G_mul_coeff_ge S0 470 (by norm_num), lhs_coeff_eq_zero 470 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_470, S0_coeff_469, S0_coeff_468, S0_coeff_467, S0_coeff_466, S0_coeff_465, S0_coeff_464, S0_coeff_463, S0_coeff_462, S0_coeff_461, S0_coeff_460, S0_coeff_459, S0_coeff_458, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_471 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 471 = (G * S0).coeff 471 := by
  rw [G_mul_coeff_ge S0 471 (by norm_num), lhs_coeff_eq_zero 471 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_471, S0_coeff_470, S0_coeff_469, S0_coeff_468, S0_coeff_467, S0_coeff_466, S0_coeff_465, S0_coeff_464, S0_coeff_463, S0_coeff_462, S0_coeff_461, S0_coeff_460, S0_coeff_459, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_472 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 472 = (G * S0).coeff 472 := by
  rw [G_mul_coeff_ge S0 472 (by norm_num), lhs_coeff_eq_zero 472 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_472, S0_coeff_471, S0_coeff_470, S0_coeff_469, S0_coeff_468, S0_coeff_467, S0_coeff_466, S0_coeff_465, S0_coeff_464, S0_coeff_463, S0_coeff_462, S0_coeff_461, S0_coeff_460, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_473 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 473 = (G * S0).coeff 473 := by
  rw [G_mul_coeff_ge S0 473 (by norm_num), lhs_coeff_eq_zero 473 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_473, S0_coeff_472, S0_coeff_471, S0_coeff_470, S0_coeff_469, S0_coeff_468, S0_coeff_467, S0_coeff_466, S0_coeff_465, S0_coeff_464, S0_coeff_463, S0_coeff_462, S0_coeff_461, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_474 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 474 = (G * S0).coeff 474 := by
  rw [G_mul_coeff_ge S0 474 (by norm_num), lhs_coeff_eq_zero 474 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_474, S0_coeff_473, S0_coeff_472, S0_coeff_471, S0_coeff_470, S0_coeff_469, S0_coeff_468, S0_coeff_467, S0_coeff_466, S0_coeff_465, S0_coeff_464, S0_coeff_463, S0_coeff_462, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_475 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 475 = (G * S0).coeff 475 := by
  rw [G_mul_coeff_ge S0 475 (by norm_num), lhs_coeff_eq_zero 475 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_475, S0_coeff_474, S0_coeff_473, S0_coeff_472, S0_coeff_471, S0_coeff_470, S0_coeff_469, S0_coeff_468, S0_coeff_467, S0_coeff_466, S0_coeff_465, S0_coeff_464, S0_coeff_463, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_476 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 476 = (G * S0).coeff 476 := by
  rw [G_mul_coeff_ge S0 476 (by norm_num), lhs_coeff_eq_zero 476 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_476, S0_coeff_475, S0_coeff_474, S0_coeff_473, S0_coeff_472, S0_coeff_471, S0_coeff_470, S0_coeff_469, S0_coeff_468, S0_coeff_467, S0_coeff_466, S0_coeff_465, S0_coeff_464, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_477 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 477 = (G * S0).coeff 477 := by
  rw [G_mul_coeff_ge S0 477 (by norm_num), lhs_coeff_eq_zero 477 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_477, S0_coeff_476, S0_coeff_475, S0_coeff_474, S0_coeff_473, S0_coeff_472, S0_coeff_471, S0_coeff_470, S0_coeff_469, S0_coeff_468, S0_coeff_467, S0_coeff_466, S0_coeff_465, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_478 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 478 = (G * S0).coeff 478 := by
  rw [G_mul_coeff_ge S0 478 (by norm_num), lhs_coeff_eq_zero 478 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_478, S0_coeff_477, S0_coeff_476, S0_coeff_475, S0_coeff_474, S0_coeff_473, S0_coeff_472, S0_coeff_471, S0_coeff_470, S0_coeff_469, S0_coeff_468, S0_coeff_467, S0_coeff_466, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_479 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 479 = (G * S0).coeff 479 := by
  rw [G_mul_coeff_ge S0 479 (by norm_num), lhs_coeff_eq_zero 479 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_479, S0_coeff_478, S0_coeff_477, S0_coeff_476, S0_coeff_475, S0_coeff_474, S0_coeff_473, S0_coeff_472, S0_coeff_471, S0_coeff_470, S0_coeff_469, S0_coeff_468, S0_coeff_467, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

lemma chain1_coeff_480 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 480 = (G * S0).coeff 480 := by
  rw [G_mul_coeff_ge S0 480 (by norm_num), lhs_coeff_eq_zero 480 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  simp only [S0_coeff_480, S0_coeff_479, S0_coeff_478, S0_coeff_477, S0_coeff_476, S0_coeff_475, S0_coeff_474, S0_coeff_473, S0_coeff_472, S0_coeff_471, S0_coeff_470, S0_coeff_469, S0_coeff_468, G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12]
  decide

/-- Uniform form of the chain-1 identity on the sixth block [401,480]. -/
theorem chain1_mid6 (n : ℕ) (h1 : 401 ≤ n) (h2 : n ≤ 480) :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff n = (G * S0).coeff n := by
  interval_cases n <;>
    first
      | exact chain1_coeff_401
      | exact chain1_coeff_402
      | exact chain1_coeff_403
      | exact chain1_coeff_404
      | exact chain1_coeff_405
      | exact chain1_coeff_406
      | exact chain1_coeff_407
      | exact chain1_coeff_408
      | exact chain1_coeff_409
      | exact chain1_coeff_410
      | exact chain1_coeff_411
      | exact chain1_coeff_412
      | exact chain1_coeff_413
      | exact chain1_coeff_414
      | exact chain1_coeff_415
      | exact chain1_coeff_416
      | exact chain1_coeff_417
      | exact chain1_coeff_418
      | exact chain1_coeff_419
      | exact chain1_coeff_420
      | exact chain1_coeff_421
      | exact chain1_coeff_422
      | exact chain1_coeff_423
      | exact chain1_coeff_424
      | exact chain1_coeff_425
      | exact chain1_coeff_426
      | exact chain1_coeff_427
      | exact chain1_coeff_428
      | exact chain1_coeff_429
      | exact chain1_coeff_430
      | exact chain1_coeff_431
      | exact chain1_coeff_432
      | exact chain1_coeff_433
      | exact chain1_coeff_434
      | exact chain1_coeff_435
      | exact chain1_coeff_436
      | exact chain1_coeff_437
      | exact chain1_coeff_438
      | exact chain1_coeff_439
      | exact chain1_coeff_440
      | exact chain1_coeff_441
      | exact chain1_coeff_442
      | exact chain1_coeff_443
      | exact chain1_coeff_444
      | exact chain1_coeff_445
      | exact chain1_coeff_446
      | exact chain1_coeff_447
      | exact chain1_coeff_448
      | exact chain1_coeff_449
      | exact chain1_coeff_450
      | exact chain1_coeff_451
      | exact chain1_coeff_452
      | exact chain1_coeff_453
      | exact chain1_coeff_454
      | exact chain1_coeff_455
      | exact chain1_coeff_456
      | exact chain1_coeff_457
      | exact chain1_coeff_458
      | exact chain1_coeff_459
      | exact chain1_coeff_460
      | exact chain1_coeff_461
      | exact chain1_coeff_462
      | exact chain1_coeff_463
      | exact chain1_coeff_464
      | exact chain1_coeff_465
      | exact chain1_coeff_466
      | exact chain1_coeff_467
      | exact chain1_coeff_468
      | exact chain1_coeff_469
      | exact chain1_coeff_470
      | exact chain1_coeff_471
      | exact chain1_coeff_472
      | exact chain1_coeff_473
      | exact chain1_coeff_474
      | exact chain1_coeff_475
      | exact chain1_coeff_476
      | exact chain1_coeff_477
      | exact chain1_coeff_478
      | exact chain1_coeff_479
      | exact chain1_coeff_480

end LeanFormal.IUT.XiFPaper.S2564Chain1Mid6Actual

end
