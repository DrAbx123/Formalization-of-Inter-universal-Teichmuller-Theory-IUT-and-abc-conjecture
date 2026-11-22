/-
S2564 chain 1: actual coefficients in degrees 321..400.

Target, for every n in [321, 400]:
  ((X : (ZMod 613)[X]) ^ 613 - T1).coeff n = (G * S0).coeff n

Since deg T1 <= 11 and n < 613, the left-hand side is -T1.coeff n = 0.
The right-hand side is expanded into its 13-term support sum
(G_mul_coeff_ge), and each S0.coeff k with 309 <= k <= 400 is looked up
through the eight shifted pieces S0_i. Only two pieces can contribute on
this window:
* 309 <= k <= 320: only S0_3 = X^241 * R3 is active, value R3.coeff (k-241);
* 321 <= k <= 400: only S0_4 = X^321 * R4 is active, value R4.coeff (k-321).
At k = 321 the S0_3 term is R3.coeff 80 = 0 because R3 has degree <= 79,
so the value is R4.coeff 0. All other pieces vanish either below their
shift or above the degree bound of their block (R0: 80, R1..R3: 79).
The resulting numeric identity in ZMod 613 is closed by decide.

Dependencies (all actual, no axioms added):
* S2560S0ShiftedPartsActual: R0..R7, S0_i, S0, S0_i_coeff;
* S2554Mod613ChainDataActual: G, T1;
* S2562GmulCoeffActual: G_mul_coeff_ge;
* S2563R3LookupActual: R3_coeff_68 .. R3_coeff_79;
* S2563R4LookupActual: R4_coeff_0 .. R4_coeff_79.

Note on names: the repository also contains root-level R0..R7 over ZMod 29,
so all references to the mod-613 blocks are written with their full name
S2560S0ShiftedPartsActual.Ri.
-/

import tmp.sheaf.xif.paper.S2560S0ShiftedPartsActual
import tmp.sheaf.xif.paper.S2554Mod613ChainDataActual
import tmp.sheaf.xif.paper.S2562GmulCoeffActual
import tmp.sheaf.xif.paper.S2563R3LookupActual
import tmp.sheaf.xif.paper.S2563R4LookupActual

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual

open LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual
open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2562GmulCoeffActual
open LeanFormal.IUT.XiFPaper.S2563R3LookupActual
open LeanFormal.IUT.XiFPaper.S2563R4LookupActual

/-! ## Degree bounds for the low blocks R0 .. R3 -/

lemma R0_natDegree_le : S2560S0ShiftedPartsActual.R0.natDegree ≤ 80 := by
  unfold S2560S0ShiftedPartsActual.R0; compute_degree!

lemma R1_natDegree_le : S2560S0ShiftedPartsActual.R1.natDegree ≤ 79 := by
  unfold S2560S0ShiftedPartsActual.R1; compute_degree!

lemma R2_natDegree_le : S2560S0ShiftedPartsActual.R2.natDegree ≤ 79 := by
  unfold S2560S0ShiftedPartsActual.R2; compute_degree!

lemma R3_natDegree_le : S2560S0ShiftedPartsActual.R3.natDegree ≤ 79 := by
  unfold S2560S0ShiftedPartsActual.R3; compute_degree!

lemma R0_coeff_zero (k : ℕ) (hk : 80 < k) :
    S2560S0ShiftedPartsActual.R0.coeff k = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have h := R0_natDegree_le
  omega

lemma R1_coeff_zero (k : ℕ) (hk : 79 < k) :
    S2560S0ShiftedPartsActual.R1.coeff k = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have h := R1_natDegree_le
  omega

lemma R2_coeff_zero (k : ℕ) (hk : 79 < k) :
    S2560S0ShiftedPartsActual.R2.coeff k = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have h := R2_natDegree_le
  omega

lemma R3_coeff_zero (k : ℕ) (hk : 79 < k) :
    S2560S0ShiftedPartsActual.R3.coeff k = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have h := R3_natDegree_le
  omega

/-! ## S0 coefficient lookup table for 309 <= k <= 400

On 309 <= k <= 320 the active piece is S0_3, on 321 <= k <= 400 it is
S0_4; every other piece is killed by a degree bound or by its shift. -/


lemma S0_coeff_309 : S0.coeff 309 = 584 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_68]

lemma S0_coeff_310 : S0.coeff 310 = 33 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_69]

lemma S0_coeff_311 : S0.coeff 311 = 2 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_70]

lemma S0_coeff_312 : S0.coeff 312 = 280 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_71]

lemma S0_coeff_313 : S0.coeff 313 = 91 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_72]

lemma S0_coeff_314 : S0.coeff 314 = 131 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_73]

lemma S0_coeff_315 : S0.coeff 315 = 416 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_74]

lemma S0_coeff_316 : S0.coeff 316 = 303 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_75]

lemma S0_coeff_317 : S0.coeff 317 = 458 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_76]

lemma S0_coeff_318 : S0.coeff 318 = 211 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_77]

lemma S0_coeff_319 : S0.coeff 319 = 280 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_78]

lemma S0_coeff_320 : S0.coeff 320 = 400 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_79]

lemma S0_coeff_321 : S0.coeff 321 = 232 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_0]

lemma S0_coeff_322 : S0.coeff 322 = 224 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_1]

lemma S0_coeff_323 : S0.coeff 323 = 245 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_2]

lemma S0_coeff_324 : S0.coeff 324 = 396 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_3]

lemma S0_coeff_325 : S0.coeff 325 = 170 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_4]

lemma S0_coeff_326 : S0.coeff 326 = 67 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_5]

lemma S0_coeff_327 : S0.coeff 327 = 261 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_6]

lemma S0_coeff_328 : S0.coeff 328 = 69 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_7]

lemma S0_coeff_329 : S0.coeff 329 = 73 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_8]

lemma S0_coeff_330 : S0.coeff 330 = 517 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_9]

lemma S0_coeff_331 : S0.coeff 331 = 329 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_10]

lemma S0_coeff_332 : S0.coeff 332 = 471 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_11]

lemma S0_coeff_333 : S0.coeff 333 = 491 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_12]

lemma S0_coeff_334 : S0.coeff 334 = 605 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_13]

lemma S0_coeff_335 : S0.coeff 335 = 375 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_14]

lemma S0_coeff_336 : S0.coeff 336 = 329 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_15]

lemma S0_coeff_337 : S0.coeff 337 = 602 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_16]

lemma S0_coeff_338 : S0.coeff 338 = 179 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_17]

lemma S0_coeff_339 : S0.coeff 339 = 462 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_18]

lemma S0_coeff_340 : S0.coeff 340 = 484 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_19]

lemma S0_coeff_341 : S0.coeff 341 = 375 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_20]

lemma S0_coeff_342 : S0.coeff 342 = 528 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_21]

lemma S0_coeff_343 : S0.coeff 343 = 404 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_22]

lemma S0_coeff_344 : S0.coeff 344 = 12 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_23]

lemma S0_coeff_345 : S0.coeff 345 = 353 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_24]

lemma S0_coeff_346 : S0.coeff 346 = 240 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_25]

lemma S0_coeff_347 : S0.coeff 347 = 374 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_26]

lemma S0_coeff_348 : S0.coeff 348 = 125 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_27]

lemma S0_coeff_349 : S0.coeff 349 = 491 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_28]

lemma S0_coeff_350 : S0.coeff 350 = 593 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_29]

lemma S0_coeff_351 : S0.coeff 351 = 453 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_30]

lemma S0_coeff_352 : S0.coeff 352 = 485 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_31]

lemma S0_coeff_353 : S0.coeff 353 = 533 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_32]

lemma S0_coeff_354 : S0.coeff 354 = 114 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_33]

lemma S0_coeff_355 : S0.coeff 355 = 494 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_34]

lemma S0_coeff_356 : S0.coeff 356 = 574 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_35]

lemma S0_coeff_357 : S0.coeff 357 = 285 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_36]

lemma S0_coeff_358 : S0.coeff 358 = 484 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_37]

lemma S0_coeff_359 : S0.coeff 359 = 20 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_38]

lemma S0_coeff_360 : S0.coeff 360 = 354 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_39]

lemma S0_coeff_361 : S0.coeff 361 = 16 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_40]

lemma S0_coeff_362 : S0.coeff 362 = 484 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_41]

lemma S0_coeff_363 : S0.coeff 363 = 452 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_42]

lemma S0_coeff_364 : S0.coeff 364 = 109 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_43]

lemma S0_coeff_365 : S0.coeff 365 = 450 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_44]

lemma S0_coeff_366 : S0.coeff 366 = 501 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_45]

lemma S0_coeff_367 : S0.coeff 367 = 467 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_46]

lemma S0_coeff_368 : S0.coeff 368 = 232 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_47]

lemma S0_coeff_369 : S0.coeff 369 = 21 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_48]

lemma S0_coeff_370 : S0.coeff 370 = 84 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_49]

lemma S0_coeff_371 : S0.coeff 371 = 18 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_50]

lemma S0_coeff_372 : S0.coeff 372 = 476 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_51]

lemma S0_coeff_373 : S0.coeff 373 = 529 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_52]

lemma S0_coeff_374 : S0.coeff 374 = 458 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_53]

lemma S0_coeff_375 : S0.coeff 375 = 265 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_54]

lemma S0_coeff_376 : S0.coeff 376 = 38 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_55]

lemma S0_coeff_377 : S0.coeff 377 = 366 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_56]

lemma S0_coeff_378 : S0.coeff 378 = 71 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_57]

lemma S0_coeff_379 : S0.coeff 379 = 605 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_58]

lemma S0_coeff_380 : S0.coeff 380 = 400 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_59]

lemma S0_coeff_381 : S0.coeff 381 = 511 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_60]

lemma S0_coeff_382 : S0.coeff 382 = 157 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_61]

lemma S0_coeff_383 : S0.coeff 383 = 109 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_62]

lemma S0_coeff_384 : S0.coeff 384 = 163 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_63]

lemma S0_coeff_385 : S0.coeff 385 = 22 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_64]

lemma S0_coeff_386 : S0.coeff 386 = 304 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_65]

lemma S0_coeff_387 : S0.coeff 387 = 75 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_66]

lemma S0_coeff_388 : S0.coeff 388 = 545 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_67]

lemma S0_coeff_389 : S0.coeff 389 = 448 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_68]

lemma S0_coeff_390 : S0.coeff 390 = 47 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_69]

lemma S0_coeff_391 : S0.coeff 391 = 7 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_70]

lemma S0_coeff_392 : S0.coeff 392 = 597 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_71]

lemma S0_coeff_393 : S0.coeff 393 = 75 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_72]

lemma S0_coeff_394 : S0.coeff 394 = 47 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_73]

lemma S0_coeff_395 : S0.coeff 395 = 204 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_74]

lemma S0_coeff_396 : S0.coeff 396 = 285 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_75]

lemma S0_coeff_397 : S0.coeff 397 = 241 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_76]

lemma S0_coeff_398 : S0.coeff 398 = 60 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_77]

lemma S0_coeff_399 : S0.coeff 399 = 597 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_78]

lemma S0_coeff_400 : S0.coeff 400 = 320 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff,
    R0_coeff_zero, R1_coeff_zero, R2_coeff_zero, R3_coeff_zero, R4_coeff_79]

/-! ## Chain 1 coefficients, degrees 321 .. 400

For each n the support sum has the 13 terms G.coeff a * S0.coeff (n - a),
a = 0..12, whose indices range over n - 12 .. n inside [309, 400]. -/

lemma chain1_coeff_321 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 321 = (G * S0).coeff 321 := by
  rw [G_mul_coeff_ge S0 321 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_321, S0_coeff_320, S0_coeff_319, S0_coeff_318, S0_coeff_317, S0_coeff_316, S0_coeff_315, S0_coeff_314, S0_coeff_313, S0_coeff_312, S0_coeff_311, S0_coeff_310, S0_coeff_309]
  simp [G, T1]
  decide

lemma chain1_coeff_322 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 322 = (G * S0).coeff 322 := by
  rw [G_mul_coeff_ge S0 322 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_322, S0_coeff_321, S0_coeff_320, S0_coeff_319, S0_coeff_318, S0_coeff_317, S0_coeff_316, S0_coeff_315, S0_coeff_314, S0_coeff_313, S0_coeff_312, S0_coeff_311, S0_coeff_310]
  simp [G, T1]
  decide

lemma chain1_coeff_323 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 323 = (G * S0).coeff 323 := by
  rw [G_mul_coeff_ge S0 323 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_323, S0_coeff_322, S0_coeff_321, S0_coeff_320, S0_coeff_319, S0_coeff_318, S0_coeff_317, S0_coeff_316, S0_coeff_315, S0_coeff_314, S0_coeff_313, S0_coeff_312, S0_coeff_311]
  simp [G, T1]
  decide

lemma chain1_coeff_324 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 324 = (G * S0).coeff 324 := by
  rw [G_mul_coeff_ge S0 324 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_324, S0_coeff_323, S0_coeff_322, S0_coeff_321, S0_coeff_320, S0_coeff_319, S0_coeff_318, S0_coeff_317, S0_coeff_316, S0_coeff_315, S0_coeff_314, S0_coeff_313, S0_coeff_312]
  simp [G, T1]
  decide

lemma chain1_coeff_325 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 325 = (G * S0).coeff 325 := by
  rw [G_mul_coeff_ge S0 325 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_325, S0_coeff_324, S0_coeff_323, S0_coeff_322, S0_coeff_321, S0_coeff_320, S0_coeff_319, S0_coeff_318, S0_coeff_317, S0_coeff_316, S0_coeff_315, S0_coeff_314, S0_coeff_313]
  simp [G, T1]
  decide

lemma chain1_coeff_326 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 326 = (G * S0).coeff 326 := by
  rw [G_mul_coeff_ge S0 326 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_326, S0_coeff_325, S0_coeff_324, S0_coeff_323, S0_coeff_322, S0_coeff_321, S0_coeff_320, S0_coeff_319, S0_coeff_318, S0_coeff_317, S0_coeff_316, S0_coeff_315, S0_coeff_314]
  simp [G, T1]
  decide

lemma chain1_coeff_327 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 327 = (G * S0).coeff 327 := by
  rw [G_mul_coeff_ge S0 327 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_327, S0_coeff_326, S0_coeff_325, S0_coeff_324, S0_coeff_323, S0_coeff_322, S0_coeff_321, S0_coeff_320, S0_coeff_319, S0_coeff_318, S0_coeff_317, S0_coeff_316, S0_coeff_315]
  simp [G, T1]
  decide

lemma chain1_coeff_328 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 328 = (G * S0).coeff 328 := by
  rw [G_mul_coeff_ge S0 328 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_328, S0_coeff_327, S0_coeff_326, S0_coeff_325, S0_coeff_324, S0_coeff_323, S0_coeff_322, S0_coeff_321, S0_coeff_320, S0_coeff_319, S0_coeff_318, S0_coeff_317, S0_coeff_316]
  simp [G, T1]
  decide

lemma chain1_coeff_329 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 329 = (G * S0).coeff 329 := by
  rw [G_mul_coeff_ge S0 329 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_329, S0_coeff_328, S0_coeff_327, S0_coeff_326, S0_coeff_325, S0_coeff_324, S0_coeff_323, S0_coeff_322, S0_coeff_321, S0_coeff_320, S0_coeff_319, S0_coeff_318, S0_coeff_317]
  simp [G, T1]
  decide

lemma chain1_coeff_330 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 330 = (G * S0).coeff 330 := by
  rw [G_mul_coeff_ge S0 330 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_330, S0_coeff_329, S0_coeff_328, S0_coeff_327, S0_coeff_326, S0_coeff_325, S0_coeff_324, S0_coeff_323, S0_coeff_322, S0_coeff_321, S0_coeff_320, S0_coeff_319, S0_coeff_318]
  simp [G, T1]
  decide

lemma chain1_coeff_331 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 331 = (G * S0).coeff 331 := by
  rw [G_mul_coeff_ge S0 331 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_331, S0_coeff_330, S0_coeff_329, S0_coeff_328, S0_coeff_327, S0_coeff_326, S0_coeff_325, S0_coeff_324, S0_coeff_323, S0_coeff_322, S0_coeff_321, S0_coeff_320, S0_coeff_319]
  simp [G, T1]
  decide

lemma chain1_coeff_332 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 332 = (G * S0).coeff 332 := by
  rw [G_mul_coeff_ge S0 332 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_332, S0_coeff_331, S0_coeff_330, S0_coeff_329, S0_coeff_328, S0_coeff_327, S0_coeff_326, S0_coeff_325, S0_coeff_324, S0_coeff_323, S0_coeff_322, S0_coeff_321, S0_coeff_320]
  simp [G, T1]
  decide

lemma chain1_coeff_333 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 333 = (G * S0).coeff 333 := by
  rw [G_mul_coeff_ge S0 333 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_333, S0_coeff_332, S0_coeff_331, S0_coeff_330, S0_coeff_329, S0_coeff_328, S0_coeff_327, S0_coeff_326, S0_coeff_325, S0_coeff_324, S0_coeff_323, S0_coeff_322, S0_coeff_321]
  simp [G, T1]
  decide

lemma chain1_coeff_334 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 334 = (G * S0).coeff 334 := by
  rw [G_mul_coeff_ge S0 334 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_334, S0_coeff_333, S0_coeff_332, S0_coeff_331, S0_coeff_330, S0_coeff_329, S0_coeff_328, S0_coeff_327, S0_coeff_326, S0_coeff_325, S0_coeff_324, S0_coeff_323, S0_coeff_322]
  simp [G, T1]
  decide

lemma chain1_coeff_335 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 335 = (G * S0).coeff 335 := by
  rw [G_mul_coeff_ge S0 335 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_335, S0_coeff_334, S0_coeff_333, S0_coeff_332, S0_coeff_331, S0_coeff_330, S0_coeff_329, S0_coeff_328, S0_coeff_327, S0_coeff_326, S0_coeff_325, S0_coeff_324, S0_coeff_323]
  simp [G, T1]
  decide

lemma chain1_coeff_336 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 336 = (G * S0).coeff 336 := by
  rw [G_mul_coeff_ge S0 336 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_336, S0_coeff_335, S0_coeff_334, S0_coeff_333, S0_coeff_332, S0_coeff_331, S0_coeff_330, S0_coeff_329, S0_coeff_328, S0_coeff_327, S0_coeff_326, S0_coeff_325, S0_coeff_324]
  simp [G, T1]
  decide

lemma chain1_coeff_337 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 337 = (G * S0).coeff 337 := by
  rw [G_mul_coeff_ge S0 337 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_337, S0_coeff_336, S0_coeff_335, S0_coeff_334, S0_coeff_333, S0_coeff_332, S0_coeff_331, S0_coeff_330, S0_coeff_329, S0_coeff_328, S0_coeff_327, S0_coeff_326, S0_coeff_325]
  simp [G, T1]
  decide

lemma chain1_coeff_338 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 338 = (G * S0).coeff 338 := by
  rw [G_mul_coeff_ge S0 338 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_338, S0_coeff_337, S0_coeff_336, S0_coeff_335, S0_coeff_334, S0_coeff_333, S0_coeff_332, S0_coeff_331, S0_coeff_330, S0_coeff_329, S0_coeff_328, S0_coeff_327, S0_coeff_326]
  simp [G, T1]
  decide

lemma chain1_coeff_339 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 339 = (G * S0).coeff 339 := by
  rw [G_mul_coeff_ge S0 339 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_339, S0_coeff_338, S0_coeff_337, S0_coeff_336, S0_coeff_335, S0_coeff_334, S0_coeff_333, S0_coeff_332, S0_coeff_331, S0_coeff_330, S0_coeff_329, S0_coeff_328, S0_coeff_327]
  simp [G, T1]
  decide

lemma chain1_coeff_340 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 340 = (G * S0).coeff 340 := by
  rw [G_mul_coeff_ge S0 340 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_340, S0_coeff_339, S0_coeff_338, S0_coeff_337, S0_coeff_336, S0_coeff_335, S0_coeff_334, S0_coeff_333, S0_coeff_332, S0_coeff_331, S0_coeff_330, S0_coeff_329, S0_coeff_328]
  simp [G, T1]
  decide

lemma chain1_coeff_341 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 341 = (G * S0).coeff 341 := by
  rw [G_mul_coeff_ge S0 341 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_341, S0_coeff_340, S0_coeff_339, S0_coeff_338, S0_coeff_337, S0_coeff_336, S0_coeff_335, S0_coeff_334, S0_coeff_333, S0_coeff_332, S0_coeff_331, S0_coeff_330, S0_coeff_329]
  simp [G, T1]
  decide

lemma chain1_coeff_342 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 342 = (G * S0).coeff 342 := by
  rw [G_mul_coeff_ge S0 342 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_342, S0_coeff_341, S0_coeff_340, S0_coeff_339, S0_coeff_338, S0_coeff_337, S0_coeff_336, S0_coeff_335, S0_coeff_334, S0_coeff_333, S0_coeff_332, S0_coeff_331, S0_coeff_330]
  simp [G, T1]
  decide

lemma chain1_coeff_343 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 343 = (G * S0).coeff 343 := by
  rw [G_mul_coeff_ge S0 343 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_343, S0_coeff_342, S0_coeff_341, S0_coeff_340, S0_coeff_339, S0_coeff_338, S0_coeff_337, S0_coeff_336, S0_coeff_335, S0_coeff_334, S0_coeff_333, S0_coeff_332, S0_coeff_331]
  simp [G, T1]
  decide

lemma chain1_coeff_344 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 344 = (G * S0).coeff 344 := by
  rw [G_mul_coeff_ge S0 344 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_344, S0_coeff_343, S0_coeff_342, S0_coeff_341, S0_coeff_340, S0_coeff_339, S0_coeff_338, S0_coeff_337, S0_coeff_336, S0_coeff_335, S0_coeff_334, S0_coeff_333, S0_coeff_332]
  simp [G, T1]
  decide

lemma chain1_coeff_345 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 345 = (G * S0).coeff 345 := by
  rw [G_mul_coeff_ge S0 345 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_345, S0_coeff_344, S0_coeff_343, S0_coeff_342, S0_coeff_341, S0_coeff_340, S0_coeff_339, S0_coeff_338, S0_coeff_337, S0_coeff_336, S0_coeff_335, S0_coeff_334, S0_coeff_333]
  simp [G, T1]
  decide

lemma chain1_coeff_346 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 346 = (G * S0).coeff 346 := by
  rw [G_mul_coeff_ge S0 346 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_346, S0_coeff_345, S0_coeff_344, S0_coeff_343, S0_coeff_342, S0_coeff_341, S0_coeff_340, S0_coeff_339, S0_coeff_338, S0_coeff_337, S0_coeff_336, S0_coeff_335, S0_coeff_334]
  simp [G, T1]
  decide

lemma chain1_coeff_347 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 347 = (G * S0).coeff 347 := by
  rw [G_mul_coeff_ge S0 347 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_347, S0_coeff_346, S0_coeff_345, S0_coeff_344, S0_coeff_343, S0_coeff_342, S0_coeff_341, S0_coeff_340, S0_coeff_339, S0_coeff_338, S0_coeff_337, S0_coeff_336, S0_coeff_335]
  simp [G, T1]
  decide

lemma chain1_coeff_348 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 348 = (G * S0).coeff 348 := by
  rw [G_mul_coeff_ge S0 348 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_348, S0_coeff_347, S0_coeff_346, S0_coeff_345, S0_coeff_344, S0_coeff_343, S0_coeff_342, S0_coeff_341, S0_coeff_340, S0_coeff_339, S0_coeff_338, S0_coeff_337, S0_coeff_336]
  simp [G, T1]
  decide

lemma chain1_coeff_349 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 349 = (G * S0).coeff 349 := by
  rw [G_mul_coeff_ge S0 349 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_349, S0_coeff_348, S0_coeff_347, S0_coeff_346, S0_coeff_345, S0_coeff_344, S0_coeff_343, S0_coeff_342, S0_coeff_341, S0_coeff_340, S0_coeff_339, S0_coeff_338, S0_coeff_337]
  simp [G, T1]
  decide

lemma chain1_coeff_350 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 350 = (G * S0).coeff 350 := by
  rw [G_mul_coeff_ge S0 350 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_350, S0_coeff_349, S0_coeff_348, S0_coeff_347, S0_coeff_346, S0_coeff_345, S0_coeff_344, S0_coeff_343, S0_coeff_342, S0_coeff_341, S0_coeff_340, S0_coeff_339, S0_coeff_338]
  simp [G, T1]
  decide

lemma chain1_coeff_351 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 351 = (G * S0).coeff 351 := by
  rw [G_mul_coeff_ge S0 351 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_351, S0_coeff_350, S0_coeff_349, S0_coeff_348, S0_coeff_347, S0_coeff_346, S0_coeff_345, S0_coeff_344, S0_coeff_343, S0_coeff_342, S0_coeff_341, S0_coeff_340, S0_coeff_339]
  simp [G, T1]
  decide

lemma chain1_coeff_352 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 352 = (G * S0).coeff 352 := by
  rw [G_mul_coeff_ge S0 352 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_352, S0_coeff_351, S0_coeff_350, S0_coeff_349, S0_coeff_348, S0_coeff_347, S0_coeff_346, S0_coeff_345, S0_coeff_344, S0_coeff_343, S0_coeff_342, S0_coeff_341, S0_coeff_340]
  simp [G, T1]
  decide

lemma chain1_coeff_353 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 353 = (G * S0).coeff 353 := by
  rw [G_mul_coeff_ge S0 353 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_353, S0_coeff_352, S0_coeff_351, S0_coeff_350, S0_coeff_349, S0_coeff_348, S0_coeff_347, S0_coeff_346, S0_coeff_345, S0_coeff_344, S0_coeff_343, S0_coeff_342, S0_coeff_341]
  simp [G, T1]
  decide

lemma chain1_coeff_354 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 354 = (G * S0).coeff 354 := by
  rw [G_mul_coeff_ge S0 354 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_354, S0_coeff_353, S0_coeff_352, S0_coeff_351, S0_coeff_350, S0_coeff_349, S0_coeff_348, S0_coeff_347, S0_coeff_346, S0_coeff_345, S0_coeff_344, S0_coeff_343, S0_coeff_342]
  simp [G, T1]
  decide

lemma chain1_coeff_355 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 355 = (G * S0).coeff 355 := by
  rw [G_mul_coeff_ge S0 355 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_355, S0_coeff_354, S0_coeff_353, S0_coeff_352, S0_coeff_351, S0_coeff_350, S0_coeff_349, S0_coeff_348, S0_coeff_347, S0_coeff_346, S0_coeff_345, S0_coeff_344, S0_coeff_343]
  simp [G, T1]
  decide

lemma chain1_coeff_356 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 356 = (G * S0).coeff 356 := by
  rw [G_mul_coeff_ge S0 356 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_356, S0_coeff_355, S0_coeff_354, S0_coeff_353, S0_coeff_352, S0_coeff_351, S0_coeff_350, S0_coeff_349, S0_coeff_348, S0_coeff_347, S0_coeff_346, S0_coeff_345, S0_coeff_344]
  simp [G, T1]
  decide

lemma chain1_coeff_357 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 357 = (G * S0).coeff 357 := by
  rw [G_mul_coeff_ge S0 357 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_357, S0_coeff_356, S0_coeff_355, S0_coeff_354, S0_coeff_353, S0_coeff_352, S0_coeff_351, S0_coeff_350, S0_coeff_349, S0_coeff_348, S0_coeff_347, S0_coeff_346, S0_coeff_345]
  simp [G, T1]
  decide

lemma chain1_coeff_358 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 358 = (G * S0).coeff 358 := by
  rw [G_mul_coeff_ge S0 358 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_358, S0_coeff_357, S0_coeff_356, S0_coeff_355, S0_coeff_354, S0_coeff_353, S0_coeff_352, S0_coeff_351, S0_coeff_350, S0_coeff_349, S0_coeff_348, S0_coeff_347, S0_coeff_346]
  simp [G, T1]
  decide

lemma chain1_coeff_359 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 359 = (G * S0).coeff 359 := by
  rw [G_mul_coeff_ge S0 359 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_359, S0_coeff_358, S0_coeff_357, S0_coeff_356, S0_coeff_355, S0_coeff_354, S0_coeff_353, S0_coeff_352, S0_coeff_351, S0_coeff_350, S0_coeff_349, S0_coeff_348, S0_coeff_347]
  simp [G, T1]
  decide

lemma chain1_coeff_360 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 360 = (G * S0).coeff 360 := by
  rw [G_mul_coeff_ge S0 360 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_360, S0_coeff_359, S0_coeff_358, S0_coeff_357, S0_coeff_356, S0_coeff_355, S0_coeff_354, S0_coeff_353, S0_coeff_352, S0_coeff_351, S0_coeff_350, S0_coeff_349, S0_coeff_348]
  simp [G, T1]
  decide

lemma chain1_coeff_361 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 361 = (G * S0).coeff 361 := by
  rw [G_mul_coeff_ge S0 361 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_361, S0_coeff_360, S0_coeff_359, S0_coeff_358, S0_coeff_357, S0_coeff_356, S0_coeff_355, S0_coeff_354, S0_coeff_353, S0_coeff_352, S0_coeff_351, S0_coeff_350, S0_coeff_349]
  simp [G, T1]
  decide

lemma chain1_coeff_362 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 362 = (G * S0).coeff 362 := by
  rw [G_mul_coeff_ge S0 362 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_362, S0_coeff_361, S0_coeff_360, S0_coeff_359, S0_coeff_358, S0_coeff_357, S0_coeff_356, S0_coeff_355, S0_coeff_354, S0_coeff_353, S0_coeff_352, S0_coeff_351, S0_coeff_350]
  simp [G, T1]
  decide

lemma chain1_coeff_363 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 363 = (G * S0).coeff 363 := by
  rw [G_mul_coeff_ge S0 363 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_363, S0_coeff_362, S0_coeff_361, S0_coeff_360, S0_coeff_359, S0_coeff_358, S0_coeff_357, S0_coeff_356, S0_coeff_355, S0_coeff_354, S0_coeff_353, S0_coeff_352, S0_coeff_351]
  simp [G, T1]
  decide

lemma chain1_coeff_364 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 364 = (G * S0).coeff 364 := by
  rw [G_mul_coeff_ge S0 364 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_364, S0_coeff_363, S0_coeff_362, S0_coeff_361, S0_coeff_360, S0_coeff_359, S0_coeff_358, S0_coeff_357, S0_coeff_356, S0_coeff_355, S0_coeff_354, S0_coeff_353, S0_coeff_352]
  simp [G, T1]
  decide

lemma chain1_coeff_365 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 365 = (G * S0).coeff 365 := by
  rw [G_mul_coeff_ge S0 365 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_365, S0_coeff_364, S0_coeff_363, S0_coeff_362, S0_coeff_361, S0_coeff_360, S0_coeff_359, S0_coeff_358, S0_coeff_357, S0_coeff_356, S0_coeff_355, S0_coeff_354, S0_coeff_353]
  simp [G, T1]
  decide

lemma chain1_coeff_366 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 366 = (G * S0).coeff 366 := by
  rw [G_mul_coeff_ge S0 366 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_366, S0_coeff_365, S0_coeff_364, S0_coeff_363, S0_coeff_362, S0_coeff_361, S0_coeff_360, S0_coeff_359, S0_coeff_358, S0_coeff_357, S0_coeff_356, S0_coeff_355, S0_coeff_354]
  simp [G, T1]
  decide

lemma chain1_coeff_367 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 367 = (G * S0).coeff 367 := by
  rw [G_mul_coeff_ge S0 367 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_367, S0_coeff_366, S0_coeff_365, S0_coeff_364, S0_coeff_363, S0_coeff_362, S0_coeff_361, S0_coeff_360, S0_coeff_359, S0_coeff_358, S0_coeff_357, S0_coeff_356, S0_coeff_355]
  simp [G, T1]
  decide

lemma chain1_coeff_368 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 368 = (G * S0).coeff 368 := by
  rw [G_mul_coeff_ge S0 368 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_368, S0_coeff_367, S0_coeff_366, S0_coeff_365, S0_coeff_364, S0_coeff_363, S0_coeff_362, S0_coeff_361, S0_coeff_360, S0_coeff_359, S0_coeff_358, S0_coeff_357, S0_coeff_356]
  simp [G, T1]
  decide

lemma chain1_coeff_369 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 369 = (G * S0).coeff 369 := by
  rw [G_mul_coeff_ge S0 369 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_369, S0_coeff_368, S0_coeff_367, S0_coeff_366, S0_coeff_365, S0_coeff_364, S0_coeff_363, S0_coeff_362, S0_coeff_361, S0_coeff_360, S0_coeff_359, S0_coeff_358, S0_coeff_357]
  simp [G, T1]
  decide

lemma chain1_coeff_370 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 370 = (G * S0).coeff 370 := by
  rw [G_mul_coeff_ge S0 370 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_370, S0_coeff_369, S0_coeff_368, S0_coeff_367, S0_coeff_366, S0_coeff_365, S0_coeff_364, S0_coeff_363, S0_coeff_362, S0_coeff_361, S0_coeff_360, S0_coeff_359, S0_coeff_358]
  simp [G, T1]
  decide

lemma chain1_coeff_371 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 371 = (G * S0).coeff 371 := by
  rw [G_mul_coeff_ge S0 371 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_371, S0_coeff_370, S0_coeff_369, S0_coeff_368, S0_coeff_367, S0_coeff_366, S0_coeff_365, S0_coeff_364, S0_coeff_363, S0_coeff_362, S0_coeff_361, S0_coeff_360, S0_coeff_359]
  simp [G, T1]
  decide

lemma chain1_coeff_372 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 372 = (G * S0).coeff 372 := by
  rw [G_mul_coeff_ge S0 372 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_372, S0_coeff_371, S0_coeff_370, S0_coeff_369, S0_coeff_368, S0_coeff_367, S0_coeff_366, S0_coeff_365, S0_coeff_364, S0_coeff_363, S0_coeff_362, S0_coeff_361, S0_coeff_360]
  simp [G, T1]
  decide

lemma chain1_coeff_373 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 373 = (G * S0).coeff 373 := by
  rw [G_mul_coeff_ge S0 373 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_373, S0_coeff_372, S0_coeff_371, S0_coeff_370, S0_coeff_369, S0_coeff_368, S0_coeff_367, S0_coeff_366, S0_coeff_365, S0_coeff_364, S0_coeff_363, S0_coeff_362, S0_coeff_361]
  simp [G, T1]
  decide

lemma chain1_coeff_374 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 374 = (G * S0).coeff 374 := by
  rw [G_mul_coeff_ge S0 374 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_374, S0_coeff_373, S0_coeff_372, S0_coeff_371, S0_coeff_370, S0_coeff_369, S0_coeff_368, S0_coeff_367, S0_coeff_366, S0_coeff_365, S0_coeff_364, S0_coeff_363, S0_coeff_362]
  simp [G, T1]
  decide

lemma chain1_coeff_375 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 375 = (G * S0).coeff 375 := by
  rw [G_mul_coeff_ge S0 375 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_375, S0_coeff_374, S0_coeff_373, S0_coeff_372, S0_coeff_371, S0_coeff_370, S0_coeff_369, S0_coeff_368, S0_coeff_367, S0_coeff_366, S0_coeff_365, S0_coeff_364, S0_coeff_363]
  simp [G, T1]
  decide

lemma chain1_coeff_376 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 376 = (G * S0).coeff 376 := by
  rw [G_mul_coeff_ge S0 376 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_376, S0_coeff_375, S0_coeff_374, S0_coeff_373, S0_coeff_372, S0_coeff_371, S0_coeff_370, S0_coeff_369, S0_coeff_368, S0_coeff_367, S0_coeff_366, S0_coeff_365, S0_coeff_364]
  simp [G, T1]
  decide

lemma chain1_coeff_377 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 377 = (G * S0).coeff 377 := by
  rw [G_mul_coeff_ge S0 377 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_377, S0_coeff_376, S0_coeff_375, S0_coeff_374, S0_coeff_373, S0_coeff_372, S0_coeff_371, S0_coeff_370, S0_coeff_369, S0_coeff_368, S0_coeff_367, S0_coeff_366, S0_coeff_365]
  simp [G, T1]
  decide

lemma chain1_coeff_378 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 378 = (G * S0).coeff 378 := by
  rw [G_mul_coeff_ge S0 378 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_378, S0_coeff_377, S0_coeff_376, S0_coeff_375, S0_coeff_374, S0_coeff_373, S0_coeff_372, S0_coeff_371, S0_coeff_370, S0_coeff_369, S0_coeff_368, S0_coeff_367, S0_coeff_366]
  simp [G, T1]
  decide

lemma chain1_coeff_379 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 379 = (G * S0).coeff 379 := by
  rw [G_mul_coeff_ge S0 379 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_379, S0_coeff_378, S0_coeff_377, S0_coeff_376, S0_coeff_375, S0_coeff_374, S0_coeff_373, S0_coeff_372, S0_coeff_371, S0_coeff_370, S0_coeff_369, S0_coeff_368, S0_coeff_367]
  simp [G, T1]
  decide

lemma chain1_coeff_380 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 380 = (G * S0).coeff 380 := by
  rw [G_mul_coeff_ge S0 380 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_380, S0_coeff_379, S0_coeff_378, S0_coeff_377, S0_coeff_376, S0_coeff_375, S0_coeff_374, S0_coeff_373, S0_coeff_372, S0_coeff_371, S0_coeff_370, S0_coeff_369, S0_coeff_368]
  simp [G, T1]
  decide

lemma chain1_coeff_381 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 381 = (G * S0).coeff 381 := by
  rw [G_mul_coeff_ge S0 381 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_381, S0_coeff_380, S0_coeff_379, S0_coeff_378, S0_coeff_377, S0_coeff_376, S0_coeff_375, S0_coeff_374, S0_coeff_373, S0_coeff_372, S0_coeff_371, S0_coeff_370, S0_coeff_369]
  simp [G, T1]
  decide

lemma chain1_coeff_382 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 382 = (G * S0).coeff 382 := by
  rw [G_mul_coeff_ge S0 382 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_382, S0_coeff_381, S0_coeff_380, S0_coeff_379, S0_coeff_378, S0_coeff_377, S0_coeff_376, S0_coeff_375, S0_coeff_374, S0_coeff_373, S0_coeff_372, S0_coeff_371, S0_coeff_370]
  simp [G, T1]
  decide

lemma chain1_coeff_383 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 383 = (G * S0).coeff 383 := by
  rw [G_mul_coeff_ge S0 383 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_383, S0_coeff_382, S0_coeff_381, S0_coeff_380, S0_coeff_379, S0_coeff_378, S0_coeff_377, S0_coeff_376, S0_coeff_375, S0_coeff_374, S0_coeff_373, S0_coeff_372, S0_coeff_371]
  simp [G, T1]
  decide

lemma chain1_coeff_384 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 384 = (G * S0).coeff 384 := by
  rw [G_mul_coeff_ge S0 384 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_384, S0_coeff_383, S0_coeff_382, S0_coeff_381, S0_coeff_380, S0_coeff_379, S0_coeff_378, S0_coeff_377, S0_coeff_376, S0_coeff_375, S0_coeff_374, S0_coeff_373, S0_coeff_372]
  simp [G, T1]
  decide

lemma chain1_coeff_385 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 385 = (G * S0).coeff 385 := by
  rw [G_mul_coeff_ge S0 385 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_385, S0_coeff_384, S0_coeff_383, S0_coeff_382, S0_coeff_381, S0_coeff_380, S0_coeff_379, S0_coeff_378, S0_coeff_377, S0_coeff_376, S0_coeff_375, S0_coeff_374, S0_coeff_373]
  simp [G, T1]
  decide

lemma chain1_coeff_386 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 386 = (G * S0).coeff 386 := by
  rw [G_mul_coeff_ge S0 386 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_386, S0_coeff_385, S0_coeff_384, S0_coeff_383, S0_coeff_382, S0_coeff_381, S0_coeff_380, S0_coeff_379, S0_coeff_378, S0_coeff_377, S0_coeff_376, S0_coeff_375, S0_coeff_374]
  simp [G, T1]
  decide

lemma chain1_coeff_387 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 387 = (G * S0).coeff 387 := by
  rw [G_mul_coeff_ge S0 387 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_387, S0_coeff_386, S0_coeff_385, S0_coeff_384, S0_coeff_383, S0_coeff_382, S0_coeff_381, S0_coeff_380, S0_coeff_379, S0_coeff_378, S0_coeff_377, S0_coeff_376, S0_coeff_375]
  simp [G, T1]
  decide

lemma chain1_coeff_388 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 388 = (G * S0).coeff 388 := by
  rw [G_mul_coeff_ge S0 388 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_388, S0_coeff_387, S0_coeff_386, S0_coeff_385, S0_coeff_384, S0_coeff_383, S0_coeff_382, S0_coeff_381, S0_coeff_380, S0_coeff_379, S0_coeff_378, S0_coeff_377, S0_coeff_376]
  simp [G, T1]
  decide

lemma chain1_coeff_389 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 389 = (G * S0).coeff 389 := by
  rw [G_mul_coeff_ge S0 389 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_389, S0_coeff_388, S0_coeff_387, S0_coeff_386, S0_coeff_385, S0_coeff_384, S0_coeff_383, S0_coeff_382, S0_coeff_381, S0_coeff_380, S0_coeff_379, S0_coeff_378, S0_coeff_377]
  simp [G, T1]
  decide

lemma chain1_coeff_390 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 390 = (G * S0).coeff 390 := by
  rw [G_mul_coeff_ge S0 390 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_390, S0_coeff_389, S0_coeff_388, S0_coeff_387, S0_coeff_386, S0_coeff_385, S0_coeff_384, S0_coeff_383, S0_coeff_382, S0_coeff_381, S0_coeff_380, S0_coeff_379, S0_coeff_378]
  simp [G, T1]
  decide

lemma chain1_coeff_391 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 391 = (G * S0).coeff 391 := by
  rw [G_mul_coeff_ge S0 391 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_391, S0_coeff_390, S0_coeff_389, S0_coeff_388, S0_coeff_387, S0_coeff_386, S0_coeff_385, S0_coeff_384, S0_coeff_383, S0_coeff_382, S0_coeff_381, S0_coeff_380, S0_coeff_379]
  simp [G, T1]
  decide

lemma chain1_coeff_392 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 392 = (G * S0).coeff 392 := by
  rw [G_mul_coeff_ge S0 392 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_392, S0_coeff_391, S0_coeff_390, S0_coeff_389, S0_coeff_388, S0_coeff_387, S0_coeff_386, S0_coeff_385, S0_coeff_384, S0_coeff_383, S0_coeff_382, S0_coeff_381, S0_coeff_380]
  simp [G, T1]
  decide

lemma chain1_coeff_393 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 393 = (G * S0).coeff 393 := by
  rw [G_mul_coeff_ge S0 393 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_393, S0_coeff_392, S0_coeff_391, S0_coeff_390, S0_coeff_389, S0_coeff_388, S0_coeff_387, S0_coeff_386, S0_coeff_385, S0_coeff_384, S0_coeff_383, S0_coeff_382, S0_coeff_381]
  simp [G, T1]
  decide

lemma chain1_coeff_394 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 394 = (G * S0).coeff 394 := by
  rw [G_mul_coeff_ge S0 394 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_394, S0_coeff_393, S0_coeff_392, S0_coeff_391, S0_coeff_390, S0_coeff_389, S0_coeff_388, S0_coeff_387, S0_coeff_386, S0_coeff_385, S0_coeff_384, S0_coeff_383, S0_coeff_382]
  simp [G, T1]
  decide

lemma chain1_coeff_395 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 395 = (G * S0).coeff 395 := by
  rw [G_mul_coeff_ge S0 395 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_395, S0_coeff_394, S0_coeff_393, S0_coeff_392, S0_coeff_391, S0_coeff_390, S0_coeff_389, S0_coeff_388, S0_coeff_387, S0_coeff_386, S0_coeff_385, S0_coeff_384, S0_coeff_383]
  simp [G, T1]
  decide

lemma chain1_coeff_396 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 396 = (G * S0).coeff 396 := by
  rw [G_mul_coeff_ge S0 396 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_396, S0_coeff_395, S0_coeff_394, S0_coeff_393, S0_coeff_392, S0_coeff_391, S0_coeff_390, S0_coeff_389, S0_coeff_388, S0_coeff_387, S0_coeff_386, S0_coeff_385, S0_coeff_384]
  simp [G, T1]
  decide

lemma chain1_coeff_397 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 397 = (G * S0).coeff 397 := by
  rw [G_mul_coeff_ge S0 397 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_397, S0_coeff_396, S0_coeff_395, S0_coeff_394, S0_coeff_393, S0_coeff_392, S0_coeff_391, S0_coeff_390, S0_coeff_389, S0_coeff_388, S0_coeff_387, S0_coeff_386, S0_coeff_385]
  simp [G, T1]
  decide

lemma chain1_coeff_398 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 398 = (G * S0).coeff 398 := by
  rw [G_mul_coeff_ge S0 398 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_398, S0_coeff_397, S0_coeff_396, S0_coeff_395, S0_coeff_394, S0_coeff_393, S0_coeff_392, S0_coeff_391, S0_coeff_390, S0_coeff_389, S0_coeff_388, S0_coeff_387, S0_coeff_386]
  simp [G, T1]
  decide

lemma chain1_coeff_399 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 399 = (G * S0).coeff 399 := by
  rw [G_mul_coeff_ge S0 399 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_399, S0_coeff_398, S0_coeff_397, S0_coeff_396, S0_coeff_395, S0_coeff_394, S0_coeff_393, S0_coeff_392, S0_coeff_391, S0_coeff_390, S0_coeff_389, S0_coeff_388, S0_coeff_387]
  simp [G, T1]
  decide

lemma chain1_coeff_400 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 400 = (G * S0).coeff 400 := by
  rw [G_mul_coeff_ge S0 400 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_400, S0_coeff_399, S0_coeff_398, S0_coeff_397, S0_coeff_396, S0_coeff_395, S0_coeff_394, S0_coeff_393, S0_coeff_392, S0_coeff_391, S0_coeff_390, S0_coeff_389, S0_coeff_388]
  simp [G, T1]
  decide

end LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual

end
