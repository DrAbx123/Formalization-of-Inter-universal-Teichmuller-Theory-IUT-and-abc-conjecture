import tmp.sheaf.xif.paper.S2560S0ShiftedPartsActual
import tmp.sheaf.xif.paper.S2554Mod613ChainDataActual
import tmp.sheaf.xif.paper.S2562GmulCoeffActual
import tmp.sheaf.xif.paper.S2563R2LookupActual
import tmp.sheaf.xif.paper.S2563R3LookupActual

/-!
# S2564Chain1Mid4Actual

Chain-1 coefficient identity for the middle range n in [241, 320]:

  ((X : (ZMod 613)[X]) ^ 613 - T1).coeff n = (G * S0).coeff n

Sources (all already verified in this repository):
* S2560S0ShiftedPartsActual  : R0..R7, S0_0..S0_7, S0 := S0_0 + ... + S0_7
* S2563R2LookupActual, S2563R3LookupActual : R_i.coeff j
* S2562GmulCoeffActual       : G_mul_coeff_ge (13-term support sum for n >= 12)
* S2554Mod613ChainDataActual : G, T1

Strategy (mirrors S2564Chain1LowActual for n < 12):
* S0 is split into 8 shifted blocks (block i starts at 81*i).
  For 229 <= k <= 320 only blocks 0, 1, 2, 3 can contribute.  Blocks 4..7
  start at 321,401,481,561 > 320; R0 has degree 80 and R1, R2 have degree 79,
  so:
    - 229 <= k <= 240 : S0.coeff k = R2.coeff (k-161)
    - 241 <= k <= 320 : S0.coeff k = R3.coeff (k-241)
  (For k <= 240 block 3 starts at 241 and is killed by the shift; for
  k >= 241 block 2 contributes R2.coeff (k-161) with k-161 >= 80, hence 0.)
* For each n in [241,320], expand (G*S0).coeff n with G_mul_coeff_ge into the
  13-term support sum, rewrite the 13 S0 lookups, and close the concrete
  ZMod 613 computation by simp [G, T1] + decide.
* Since n < 613, ((X)^613).coeff n = 0, so the left hand side is -T1.coeff n
  (and T1 has degree 11, so for these n it is 0 as well).

Note on names: references to the mod-613 R0, R1, R2, R3 are written with their
full name to avoid clashing with the root-level R0, R1 from an unrelated
mod-29 development.
-/

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual

open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual
open LeanFormal.IUT.XiFPaper.S2562GmulCoeffActual
open LeanFormal.IUT.XiFPaper.S2563R2LookupActual
open LeanFormal.IUT.XiFPaper.S2563R3LookupActual

/-- R0 has degree at most 80, so its coefficients vanish beyond 80. -/
lemma R0_natDegree_le : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.natDegree ≤ 80 := by unfold LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0; compute_degree!

/-- R1 has degree at most 79, so its coefficients vanish beyond 79. -/
lemma R1_natDegree_le : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.natDegree ≤ 79 := by unfold LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1; compute_degree!

/-- R2 has degree at most 79, so its coefficients vanish beyond 79. -/
lemma R2_natDegree_le : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R2.natDegree ≤ 79 := by unfold LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R2; compute_degree!

lemma coeff_zero_of_natDegree_le {P : (ZMod 613)[X]} {d m : ℕ} (hd : P.natDegree ≤ d) (hm : d < m) :
    P.coeff m = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

lemma R0_coeff_eq_zero_of_gt (m : ℕ) (hm : 80 < m) : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff m = 0 :=
  coeff_zero_of_natDegree_le R0_natDegree_le hm

lemma R1_coeff_eq_zero_of_gt (m : ℕ) (hm : 79 < m) : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff m = 0 :=
  coeff_zero_of_natDegree_le R1_natDegree_le hm

lemma R2_coeff_eq_zero_of_gt (m : ℕ) (hm : 79 < m) : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R2.coeff m = 0 :=
  coeff_zero_of_natDegree_le R2_natDegree_le hm

/-! ## S0 coefficient lookup on 229 .. 320 -/

/-- On the window [229,240] only the third block of S0 contributes. -/
lemma S0_coeff_229_240 (k : ℕ) (hk1 : 229 ≤ k) (hk2 : k ≤ 240) :
    S0.coeff k = LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R2.coeff (k - 161) := by
  have h0 : S0_0.coeff k = 0 := by
    rw [S0_0_coeff, if_pos (by omega : (0 : ℕ) ≤ k), Nat.sub_zero]
    exact R0_coeff_eq_zero_of_gt k (by omega)
  have h1 : S0_1.coeff k = 0 := by
    rw [S0_1_coeff, if_pos (by omega : (81 : ℕ) ≤ k)]
    exact R1_coeff_eq_zero_of_gt (k - 81) (by omega)
  have h2 : S0_2.coeff k = LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R2.coeff (k - 161) := by
    rw [S0_2_coeff, if_pos (by omega : (161 : ℕ) ≤ k)]
  have h3 : S0_3.coeff k = 0 := by
    rw [S0_3_coeff, if_neg (by omega : ¬ (241 : ℕ) ≤ k)]
  have h4 : S0_4.coeff k = 0 := by
    rw [S0_4_coeff, if_neg (by omega : ¬ (321 : ℕ) ≤ k)]
  have h5 : S0_5.coeff k = 0 := by
    rw [S0_5_coeff, if_neg (by omega : ¬ (401 : ℕ) ≤ k)]
  have h6 : S0_6.coeff k = 0 := by
    rw [S0_6_coeff, if_neg (by omega : ¬ (481 : ℕ) ≤ k)]
  have h7 : S0_7.coeff k = 0 := by
    rw [S0_7_coeff, if_neg (by omega : ¬ (561 : ℕ) ≤ k)]
  rw [S0]
  simp only [Polynomial.coeff_add, h0, h1, h2, h3, h4, h5, h6, h7, zero_add, add_zero]

/-- On the window [241,320] only the fourth block of S0 contributes. -/
lemma S0_coeff_241_320 (k : ℕ) (hk1 : 241 ≤ k) (hk2 : k ≤ 320) :
    S0.coeff k = LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R3.coeff (k - 241) := by
  have h0 : S0_0.coeff k = 0 := by
    rw [S0_0_coeff, if_pos (by omega : (0 : ℕ) ≤ k), Nat.sub_zero]
    exact R0_coeff_eq_zero_of_gt k (by omega)
  have h1 : S0_1.coeff k = 0 := by
    rw [S0_1_coeff, if_pos (by omega : (81 : ℕ) ≤ k)]
    exact R1_coeff_eq_zero_of_gt (k - 81) (by omega)
  have h2 : S0_2.coeff k = 0 := by
    rw [S0_2_coeff, if_pos (by omega : (161 : ℕ) ≤ k)]
    exact R2_coeff_eq_zero_of_gt (k - 161) (by omega)
  have h3 : S0_3.coeff k = LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R3.coeff (k - 241) := by
    rw [S0_3_coeff, if_pos (by omega : (241 : ℕ) ≤ k)]
  have h4 : S0_4.coeff k = 0 := by
    rw [S0_4_coeff, if_neg (by omega : ¬ (321 : ℕ) ≤ k)]
  have h5 : S0_5.coeff k = 0 := by
    rw [S0_5_coeff, if_neg (by omega : ¬ (401 : ℕ) ≤ k)]
  have h6 : S0_6.coeff k = 0 := by
    rw [S0_6_coeff, if_neg (by omega : ¬ (481 : ℕ) ≤ k)]
  have h7 : S0_7.coeff k = 0 := by
    rw [S0_7_coeff, if_neg (by omega : ¬ (561 : ℕ) ≤ k)]
  rw [S0]
  simp only [Polynomial.coeff_add, h0, h1, h2, h3, h4, h5, h6, h7, zero_add, add_zero]

lemma S0_coeff_229 : S0.coeff 229 = 417 := by
  rw [S0_coeff_229_240 229 (by norm_num) (by norm_num)]
  exact R2_coeff_68

lemma S0_coeff_230 : S0.coeff 230 = 477 := by
  rw [S0_coeff_229_240 230 (by norm_num) (by norm_num)]
  exact R2_coeff_69

lemma S0_coeff_231 : S0.coeff 231 = 386 := by
  rw [S0_coeff_229_240 231 (by norm_num) (by norm_num)]
  exact R2_coeff_70

lemma S0_coeff_232 : S0.coeff 232 = 369 := by
  rw [S0_coeff_229_240 232 (by norm_num) (by norm_num)]
  exact R2_coeff_71

lemma S0_coeff_233 : S0.coeff 233 = 110 := by
  rw [S0_coeff_229_240 233 (by norm_num) (by norm_num)]
  exact R2_coeff_72

lemma S0_coeff_234 : S0.coeff 234 = 172 := by
  rw [S0_coeff_229_240 234 (by norm_num) (by norm_num)]
  exact R2_coeff_73

lemma S0_coeff_235 : S0.coeff 235 = 358 := by
  rw [S0_coeff_229_240 235 (by norm_num) (by norm_num)]
  exact R2_coeff_74

lemma S0_coeff_236 : S0.coeff 236 = 512 := by
  rw [S0_coeff_229_240 236 (by norm_num) (by norm_num)]
  exact R2_coeff_75

lemma S0_coeff_237 : S0.coeff 237 = 397 := by
  rw [S0_coeff_229_240 237 (by norm_num) (by norm_num)]
  exact R2_coeff_76

lemma S0_coeff_238 : S0.coeff 238 = 431 := by
  rw [S0_coeff_229_240 238 (by norm_num) (by norm_num)]
  exact R2_coeff_77

lemma S0_coeff_239 : S0.coeff 239 = 456 := by
  rw [S0_coeff_229_240 239 (by norm_num) (by norm_num)]
  exact R2_coeff_78

lemma S0_coeff_240 : S0.coeff 240 = 455 := by
  rw [S0_coeff_229_240 240 (by norm_num) (by norm_num)]
  exact R2_coeff_79

lemma S0_coeff_241 : S0.coeff 241 = 426 := by
  rw [S0_coeff_241_320 241 (by norm_num) (by norm_num)]
  exact R3_coeff_0

lemma S0_coeff_242 : S0.coeff 242 = 595 := by
  rw [S0_coeff_241_320 242 (by norm_num) (by norm_num)]
  exact R3_coeff_1

lemma S0_coeff_243 : S0.coeff 243 = 14 := by
  rw [S0_coeff_241_320 243 (by norm_num) (by norm_num)]
  exact R3_coeff_2

lemma S0_coeff_244 : S0.coeff 244 = 2 := by
  rw [S0_coeff_241_320 244 (by norm_num) (by norm_num)]
  exact R3_coeff_3

lemma S0_coeff_245 : S0.coeff 245 = 544 := by
  rw [S0_coeff_241_320 245 (by norm_num) (by norm_num)]
  exact R3_coeff_4

lemma S0_coeff_246 : S0.coeff 246 = 133 := by
  rw [S0_coeff_241_320 246 (by norm_num) (by norm_num)]
  exact R3_coeff_5

lemma S0_coeff_247 : S0.coeff 247 = 455 := by
  rw [S0_coeff_241_320 247 (by norm_num) (by norm_num)]
  exact R3_coeff_6

lemma S0_coeff_248 : S0.coeff 248 = 556 := by
  rw [S0_coeff_241_320 248 (by norm_num) (by norm_num)]
  exact R3_coeff_7

lemma S0_coeff_249 : S0.coeff 249 = 243 := by
  rw [S0_coeff_241_320 249 (by norm_num) (by norm_num)]
  exact R3_coeff_8

lemma S0_coeff_250 : S0.coeff 250 = 558 := by
  rw [S0_coeff_241_320 250 (by norm_num) (by norm_num)]
  exact R3_coeff_9

lemma S0_coeff_251 : S0.coeff 251 = 211 := by
  rw [S0_coeff_241_320 251 (by norm_num) (by norm_num)]
  exact R3_coeff_10

lemma S0_coeff_252 : S0.coeff 252 = 226 := by
  rw [S0_coeff_241_320 252 (by norm_num) (by norm_num)]
  exact R3_coeff_11

lemma S0_coeff_253 : S0.coeff 253 = 413 := by
  rw [S0_coeff_241_320 253 (by norm_num) (by norm_num)]
  exact R3_coeff_12

lemma S0_coeff_254 : S0.coeff 254 = 406 := by
  rw [S0_coeff_241_320 254 (by norm_num) (by norm_num)]
  exact R3_coeff_13

lemma S0_coeff_255 : S0.coeff 255 = 266 := by
  rw [S0_coeff_241_320 255 (by norm_num) (by norm_num)]
  exact R3_coeff_14

lemma S0_coeff_256 : S0.coeff 256 = 460 := by
  rw [S0_coeff_241_320 256 (by norm_num) (by norm_num)]
  exact R3_coeff_15

lemma S0_coeff_257 : S0.coeff 257 = 517 := by
  rw [S0_coeff_241_320 257 (by norm_num) (by norm_num)]
  exact R3_coeff_16

lemma S0_coeff_258 : S0.coeff 258 = 36 := by
  rw [S0_coeff_241_320 258 (by norm_num) (by norm_num)]
  exact R3_coeff_17

lemma S0_coeff_259 : S0.coeff 259 = 38 := by
  rw [S0_coeff_241_320 259 (by norm_num) (by norm_num)]
  exact R3_coeff_18

lemma S0_coeff_260 : S0.coeff 260 = 212 := by
  rw [S0_coeff_241_320 260 (by norm_num) (by norm_num)]
  exact R3_coeff_19

lemma S0_coeff_261 : S0.coeff 261 = 218 := by
  rw [S0_coeff_241_320 261 (by norm_num) (by norm_num)]
  exact R3_coeff_20

lemma S0_coeff_262 : S0.coeff 262 = 552 := by
  rw [S0_coeff_241_320 262 (by norm_num) (by norm_num)]
  exact R3_coeff_21

lemma S0_coeff_263 : S0.coeff 263 = 410 := by
  rw [S0_coeff_241_320 263 (by norm_num) (by norm_num)]
  exact R3_coeff_22

lemma S0_coeff_264 : S0.coeff 264 = 198 := by
  rw [S0_coeff_241_320 264 (by norm_num) (by norm_num)]
  exact R3_coeff_23

lemma S0_coeff_265 : S0.coeff 265 = 518 := by
  rw [S0_coeff_241_320 265 (by norm_num) (by norm_num)]
  exact R3_coeff_24

lemma S0_coeff_266 : S0.coeff 266 = 373 := by
  rw [S0_coeff_241_320 266 (by norm_num) (by norm_num)]
  exact R3_coeff_25

lemma S0_coeff_267 : S0.coeff 267 = 199 := by
  rw [S0_coeff_241_320 267 (by norm_num) (by norm_num)]
  exact R3_coeff_26

lemma S0_coeff_268 : S0.coeff 268 = 205 := by
  rw [S0_coeff_241_320 268 (by norm_num) (by norm_num)]
  exact R3_coeff_27

lemma S0_coeff_269 : S0.coeff 269 = 407 := by
  rw [S0_coeff_241_320 269 (by norm_num) (by norm_num)]
  exact R3_coeff_28

lemma S0_coeff_270 : S0.coeff 270 = 144 := by
  rw [S0_coeff_241_320 270 (by norm_num) (by norm_num)]
  exact R3_coeff_29

lemma S0_coeff_271 : S0.coeff 271 = 586 := by
  rw [S0_coeff_241_320 271 (by norm_num) (by norm_num)]
  exact R3_coeff_30

lemma S0_coeff_272 : S0.coeff 272 = 69 := by
  rw [S0_coeff_241_320 272 (by norm_num) (by norm_num)]
  exact R3_coeff_31

lemma S0_coeff_273 : S0.coeff 273 = 522 := by
  rw [S0_coeff_241_320 273 (by norm_num) (by norm_num)]
  exact R3_coeff_32

lemma S0_coeff_274 : S0.coeff 274 = 216 := by
  rw [S0_coeff_241_320 274 (by norm_num) (by norm_num)]
  exact R3_coeff_33

lemma S0_coeff_275 : S0.coeff 275 = 6 := by
  rw [S0_coeff_241_320 275 (by norm_num) (by norm_num)]
  exact R3_coeff_34

lemma S0_coeff_276 : S0.coeff 276 = 320 := by
  rw [S0_coeff_241_320 276 (by norm_num) (by norm_num)]
  exact R3_coeff_35

lemma S0_coeff_277 : S0.coeff 277 = 300 := by
  rw [S0_coeff_241_320 277 (by norm_num) (by norm_num)]
  exact R3_coeff_36

lemma S0_coeff_278 : S0.coeff 278 = 417 := by
  rw [S0_coeff_241_320 278 (by norm_num) (by norm_num)]
  exact R3_coeff_37

lemma S0_coeff_279 : S0.coeff 279 = 136 := by
  rw [S0_coeff_241_320 279 (by norm_num) (by norm_num)]
  exact R3_coeff_38

lemma S0_coeff_280 : S0.coeff 280 = 289 := by
  rw [S0_coeff_241_320 280 (by norm_num) (by norm_num)]
  exact R3_coeff_39

lemma S0_coeff_281 : S0.coeff 281 = 518 := by
  rw [S0_coeff_241_320 281 (by norm_num) (by norm_num)]
  exact R3_coeff_40

lemma S0_coeff_282 : S0.coeff 282 = 469 := by
  rw [S0_coeff_241_320 282 (by norm_num) (by norm_num)]
  exact R3_coeff_41

lemma S0_coeff_283 : S0.coeff 283 = 4 := by
  rw [S0_coeff_241_320 283 (by norm_num) (by norm_num)]
  exact R3_coeff_42

lemma S0_coeff_284 : S0.coeff 284 = 6 := by
  rw [S0_coeff_241_320 284 (by norm_num) (by norm_num)]
  exact R3_coeff_43

lemma S0_coeff_285 : S0.coeff 285 = 242 := by
  rw [S0_coeff_241_320 285 (by norm_num) (by norm_num)]
  exact R3_coeff_44

lemma S0_coeff_286 : S0.coeff 286 = 7 := by
  rw [S0_coeff_241_320 286 (by norm_num) (by norm_num)]
  exact R3_coeff_45

lemma S0_coeff_287 : S0.coeff 287 = 60 := by
  rw [S0_coeff_241_320 287 (by norm_num) (by norm_num)]
  exact R3_coeff_46

lemma S0_coeff_288 : S0.coeff 288 = 141 := by
  rw [S0_coeff_241_320 288 (by norm_num) (by norm_num)]
  exact R3_coeff_47

lemma S0_coeff_289 : S0.coeff 289 = 243 := by
  rw [S0_coeff_241_320 289 (by norm_num) (by norm_num)]
  exact R3_coeff_48

lemma S0_coeff_290 : S0.coeff 290 = 10 := by
  rw [S0_coeff_241_320 290 (by norm_num) (by norm_num)]
  exact R3_coeff_49

lemma S0_coeff_291 : S0.coeff 291 = 462 := by
  rw [S0_coeff_241_320 291 (by norm_num) (by norm_num)]
  exact R3_coeff_50

lemma S0_coeff_292 : S0.coeff 292 = 439 := by
  rw [S0_coeff_241_320 292 (by norm_num) (by norm_num)]
  exact R3_coeff_51

lemma S0_coeff_293 : S0.coeff 293 = 401 := by
  rw [S0_coeff_241_320 293 (by norm_num) (by norm_num)]
  exact R3_coeff_52

lemma S0_coeff_294 : S0.coeff 294 = 479 := by
  rw [S0_coeff_241_320 294 (by norm_num) (by norm_num)]
  exact R3_coeff_53

lemma S0_coeff_295 : S0.coeff 295 = 141 := by
  rw [S0_coeff_241_320 295 (by norm_num) (by norm_num)]
  exact R3_coeff_54

lemma S0_coeff_296 : S0.coeff 296 = 47 := by
  rw [S0_coeff_241_320 296 (by norm_num) (by norm_num)]
  exact R3_coeff_55

lemma S0_coeff_297 : S0.coeff 297 = 356 := by
  rw [S0_coeff_241_320 297 (by norm_num) (by norm_num)]
  exact R3_coeff_56

lemma S0_coeff_298 : S0.coeff 298 = 191 := by
  rw [S0_coeff_241_320 298 (by norm_num) (by norm_num)]
  exact R3_coeff_57

lemma S0_coeff_299 : S0.coeff 299 = 406 := by
  rw [S0_coeff_241_320 299 (by norm_num) (by norm_num)]
  exact R3_coeff_58

lemma S0_coeff_300 : S0.coeff 300 = 545 := by
  rw [S0_coeff_241_320 300 (by norm_num) (by norm_num)]
  exact R3_coeff_59

lemma S0_coeff_301 : S0.coeff 301 = 563 := by
  rw [S0_coeff_241_320 301 (by norm_num) (by norm_num)]
  exact R3_coeff_60

lemma S0_coeff_302 : S0.coeff 302 = 301 := by
  rw [S0_coeff_241_320 302 (by norm_num) (by norm_num)]
  exact R3_coeff_61

lemma S0_coeff_303 : S0.coeff 303 = 294 := by
  rw [S0_coeff_241_320 303 (by norm_num) (by norm_num)]
  exact R3_coeff_62

lemma S0_coeff_304 : S0.coeff 304 = 476 := by
  rw [S0_coeff_241_320 304 (by norm_num) (by norm_num)]
  exact R3_coeff_63

lemma S0_coeff_305 : S0.coeff 305 = 284 := by
  rw [S0_coeff_241_320 305 (by norm_num) (by norm_num)]
  exact R3_coeff_64

lemma S0_coeff_306 : S0.coeff 306 = 202 := by
  rw [S0_coeff_241_320 306 (by norm_num) (by norm_num)]
  exact R3_coeff_65

lemma S0_coeff_307 : S0.coeff 307 = 403 := by
  rw [S0_coeff_241_320 307 (by norm_num) (by norm_num)]
  exact R3_coeff_66

lemma S0_coeff_308 : S0.coeff 308 = 209 := by
  rw [S0_coeff_241_320 308 (by norm_num) (by norm_num)]
  exact R3_coeff_67

lemma S0_coeff_309 : S0.coeff 309 = 584 := by
  rw [S0_coeff_241_320 309 (by norm_num) (by norm_num)]
  exact R3_coeff_68

lemma S0_coeff_310 : S0.coeff 310 = 33 := by
  rw [S0_coeff_241_320 310 (by norm_num) (by norm_num)]
  exact R3_coeff_69

lemma S0_coeff_311 : S0.coeff 311 = 2 := by
  rw [S0_coeff_241_320 311 (by norm_num) (by norm_num)]
  exact R3_coeff_70

lemma S0_coeff_312 : S0.coeff 312 = 280 := by
  rw [S0_coeff_241_320 312 (by norm_num) (by norm_num)]
  exact R3_coeff_71

lemma S0_coeff_313 : S0.coeff 313 = 91 := by
  rw [S0_coeff_241_320 313 (by norm_num) (by norm_num)]
  exact R3_coeff_72

lemma S0_coeff_314 : S0.coeff 314 = 131 := by
  rw [S0_coeff_241_320 314 (by norm_num) (by norm_num)]
  exact R3_coeff_73

lemma S0_coeff_315 : S0.coeff 315 = 416 := by
  rw [S0_coeff_241_320 315 (by norm_num) (by norm_num)]
  exact R3_coeff_74

lemma S0_coeff_316 : S0.coeff 316 = 303 := by
  rw [S0_coeff_241_320 316 (by norm_num) (by norm_num)]
  exact R3_coeff_75

lemma S0_coeff_317 : S0.coeff 317 = 458 := by
  rw [S0_coeff_241_320 317 (by norm_num) (by norm_num)]
  exact R3_coeff_76

lemma S0_coeff_318 : S0.coeff 318 = 211 := by
  rw [S0_coeff_241_320 318 (by norm_num) (by norm_num)]
  exact R3_coeff_77

lemma S0_coeff_319 : S0.coeff 319 = 280 := by
  rw [S0_coeff_241_320 319 (by norm_num) (by norm_num)]
  exact R3_coeff_78

lemma S0_coeff_320 : S0.coeff 320 = 400 := by
  rw [S0_coeff_241_320 320 (by norm_num) (by norm_num)]
  exact R3_coeff_79

/-! ## Chain-1 coefficient identity on 241 .. 320 -/

lemma chain1_coeff_241 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 241 = (G * S0).coeff 241 := by
  rw [G_mul_coeff_ge S0 241 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_241, S0_coeff_240, S0_coeff_239, S0_coeff_238, S0_coeff_237, S0_coeff_236, S0_coeff_235, S0_coeff_234, S0_coeff_233, S0_coeff_232, S0_coeff_231, S0_coeff_230, S0_coeff_229]
  simp [G, T1]
  decide

lemma chain1_coeff_242 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 242 = (G * S0).coeff 242 := by
  rw [G_mul_coeff_ge S0 242 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_242, S0_coeff_241, S0_coeff_240, S0_coeff_239, S0_coeff_238, S0_coeff_237, S0_coeff_236, S0_coeff_235, S0_coeff_234, S0_coeff_233, S0_coeff_232, S0_coeff_231, S0_coeff_230]
  simp [G, T1]
  decide

lemma chain1_coeff_243 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 243 = (G * S0).coeff 243 := by
  rw [G_mul_coeff_ge S0 243 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_243, S0_coeff_242, S0_coeff_241, S0_coeff_240, S0_coeff_239, S0_coeff_238, S0_coeff_237, S0_coeff_236, S0_coeff_235, S0_coeff_234, S0_coeff_233, S0_coeff_232, S0_coeff_231]
  simp [G, T1]
  decide

lemma chain1_coeff_244 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 244 = (G * S0).coeff 244 := by
  rw [G_mul_coeff_ge S0 244 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_244, S0_coeff_243, S0_coeff_242, S0_coeff_241, S0_coeff_240, S0_coeff_239, S0_coeff_238, S0_coeff_237, S0_coeff_236, S0_coeff_235, S0_coeff_234, S0_coeff_233, S0_coeff_232]
  simp [G, T1]
  decide

lemma chain1_coeff_245 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 245 = (G * S0).coeff 245 := by
  rw [G_mul_coeff_ge S0 245 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_245, S0_coeff_244, S0_coeff_243, S0_coeff_242, S0_coeff_241, S0_coeff_240, S0_coeff_239, S0_coeff_238, S0_coeff_237, S0_coeff_236, S0_coeff_235, S0_coeff_234, S0_coeff_233]
  simp [G, T1]
  decide

lemma chain1_coeff_246 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 246 = (G * S0).coeff 246 := by
  rw [G_mul_coeff_ge S0 246 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_246, S0_coeff_245, S0_coeff_244, S0_coeff_243, S0_coeff_242, S0_coeff_241, S0_coeff_240, S0_coeff_239, S0_coeff_238, S0_coeff_237, S0_coeff_236, S0_coeff_235, S0_coeff_234]
  simp [G, T1]
  decide

lemma chain1_coeff_247 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 247 = (G * S0).coeff 247 := by
  rw [G_mul_coeff_ge S0 247 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_247, S0_coeff_246, S0_coeff_245, S0_coeff_244, S0_coeff_243, S0_coeff_242, S0_coeff_241, S0_coeff_240, S0_coeff_239, S0_coeff_238, S0_coeff_237, S0_coeff_236, S0_coeff_235]
  simp [G, T1]
  decide

lemma chain1_coeff_248 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 248 = (G * S0).coeff 248 := by
  rw [G_mul_coeff_ge S0 248 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_248, S0_coeff_247, S0_coeff_246, S0_coeff_245, S0_coeff_244, S0_coeff_243, S0_coeff_242, S0_coeff_241, S0_coeff_240, S0_coeff_239, S0_coeff_238, S0_coeff_237, S0_coeff_236]
  simp [G, T1]
  decide

lemma chain1_coeff_249 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 249 = (G * S0).coeff 249 := by
  rw [G_mul_coeff_ge S0 249 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_249, S0_coeff_248, S0_coeff_247, S0_coeff_246, S0_coeff_245, S0_coeff_244, S0_coeff_243, S0_coeff_242, S0_coeff_241, S0_coeff_240, S0_coeff_239, S0_coeff_238, S0_coeff_237]
  simp [G, T1]
  decide

lemma chain1_coeff_250 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 250 = (G * S0).coeff 250 := by
  rw [G_mul_coeff_ge S0 250 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_250, S0_coeff_249, S0_coeff_248, S0_coeff_247, S0_coeff_246, S0_coeff_245, S0_coeff_244, S0_coeff_243, S0_coeff_242, S0_coeff_241, S0_coeff_240, S0_coeff_239, S0_coeff_238]
  simp [G, T1]
  decide

lemma chain1_coeff_251 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 251 = (G * S0).coeff 251 := by
  rw [G_mul_coeff_ge S0 251 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_251, S0_coeff_250, S0_coeff_249, S0_coeff_248, S0_coeff_247, S0_coeff_246, S0_coeff_245, S0_coeff_244, S0_coeff_243, S0_coeff_242, S0_coeff_241, S0_coeff_240, S0_coeff_239]
  simp [G, T1]
  decide

lemma chain1_coeff_252 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 252 = (G * S0).coeff 252 := by
  rw [G_mul_coeff_ge S0 252 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_252, S0_coeff_251, S0_coeff_250, S0_coeff_249, S0_coeff_248, S0_coeff_247, S0_coeff_246, S0_coeff_245, S0_coeff_244, S0_coeff_243, S0_coeff_242, S0_coeff_241, S0_coeff_240]
  simp [G, T1]
  decide

lemma chain1_coeff_253 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 253 = (G * S0).coeff 253 := by
  rw [G_mul_coeff_ge S0 253 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_253, S0_coeff_252, S0_coeff_251, S0_coeff_250, S0_coeff_249, S0_coeff_248, S0_coeff_247, S0_coeff_246, S0_coeff_245, S0_coeff_244, S0_coeff_243, S0_coeff_242, S0_coeff_241]
  simp [G, T1]
  decide

lemma chain1_coeff_254 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 254 = (G * S0).coeff 254 := by
  rw [G_mul_coeff_ge S0 254 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_254, S0_coeff_253, S0_coeff_252, S0_coeff_251, S0_coeff_250, S0_coeff_249, S0_coeff_248, S0_coeff_247, S0_coeff_246, S0_coeff_245, S0_coeff_244, S0_coeff_243, S0_coeff_242]
  simp [G, T1]
  decide

lemma chain1_coeff_255 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 255 = (G * S0).coeff 255 := by
  rw [G_mul_coeff_ge S0 255 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_255, S0_coeff_254, S0_coeff_253, S0_coeff_252, S0_coeff_251, S0_coeff_250, S0_coeff_249, S0_coeff_248, S0_coeff_247, S0_coeff_246, S0_coeff_245, S0_coeff_244, S0_coeff_243]
  simp [G, T1]
  decide

lemma chain1_coeff_256 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 256 = (G * S0).coeff 256 := by
  rw [G_mul_coeff_ge S0 256 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_256, S0_coeff_255, S0_coeff_254, S0_coeff_253, S0_coeff_252, S0_coeff_251, S0_coeff_250, S0_coeff_249, S0_coeff_248, S0_coeff_247, S0_coeff_246, S0_coeff_245, S0_coeff_244]
  simp [G, T1]
  decide

lemma chain1_coeff_257 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 257 = (G * S0).coeff 257 := by
  rw [G_mul_coeff_ge S0 257 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_257, S0_coeff_256, S0_coeff_255, S0_coeff_254, S0_coeff_253, S0_coeff_252, S0_coeff_251, S0_coeff_250, S0_coeff_249, S0_coeff_248, S0_coeff_247, S0_coeff_246, S0_coeff_245]
  simp [G, T1]
  decide

lemma chain1_coeff_258 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 258 = (G * S0).coeff 258 := by
  rw [G_mul_coeff_ge S0 258 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_258, S0_coeff_257, S0_coeff_256, S0_coeff_255, S0_coeff_254, S0_coeff_253, S0_coeff_252, S0_coeff_251, S0_coeff_250, S0_coeff_249, S0_coeff_248, S0_coeff_247, S0_coeff_246]
  simp [G, T1]
  decide

lemma chain1_coeff_259 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 259 = (G * S0).coeff 259 := by
  rw [G_mul_coeff_ge S0 259 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_259, S0_coeff_258, S0_coeff_257, S0_coeff_256, S0_coeff_255, S0_coeff_254, S0_coeff_253, S0_coeff_252, S0_coeff_251, S0_coeff_250, S0_coeff_249, S0_coeff_248, S0_coeff_247]
  simp [G, T1]
  decide

lemma chain1_coeff_260 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 260 = (G * S0).coeff 260 := by
  rw [G_mul_coeff_ge S0 260 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_260, S0_coeff_259, S0_coeff_258, S0_coeff_257, S0_coeff_256, S0_coeff_255, S0_coeff_254, S0_coeff_253, S0_coeff_252, S0_coeff_251, S0_coeff_250, S0_coeff_249, S0_coeff_248]
  simp [G, T1]
  decide

lemma chain1_coeff_261 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 261 = (G * S0).coeff 261 := by
  rw [G_mul_coeff_ge S0 261 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_261, S0_coeff_260, S0_coeff_259, S0_coeff_258, S0_coeff_257, S0_coeff_256, S0_coeff_255, S0_coeff_254, S0_coeff_253, S0_coeff_252, S0_coeff_251, S0_coeff_250, S0_coeff_249]
  simp [G, T1]
  decide

lemma chain1_coeff_262 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 262 = (G * S0).coeff 262 := by
  rw [G_mul_coeff_ge S0 262 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_262, S0_coeff_261, S0_coeff_260, S0_coeff_259, S0_coeff_258, S0_coeff_257, S0_coeff_256, S0_coeff_255, S0_coeff_254, S0_coeff_253, S0_coeff_252, S0_coeff_251, S0_coeff_250]
  simp [G, T1]
  decide

lemma chain1_coeff_263 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 263 = (G * S0).coeff 263 := by
  rw [G_mul_coeff_ge S0 263 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_263, S0_coeff_262, S0_coeff_261, S0_coeff_260, S0_coeff_259, S0_coeff_258, S0_coeff_257, S0_coeff_256, S0_coeff_255, S0_coeff_254, S0_coeff_253, S0_coeff_252, S0_coeff_251]
  simp [G, T1]
  decide

lemma chain1_coeff_264 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 264 = (G * S0).coeff 264 := by
  rw [G_mul_coeff_ge S0 264 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_264, S0_coeff_263, S0_coeff_262, S0_coeff_261, S0_coeff_260, S0_coeff_259, S0_coeff_258, S0_coeff_257, S0_coeff_256, S0_coeff_255, S0_coeff_254, S0_coeff_253, S0_coeff_252]
  simp [G, T1]
  decide

lemma chain1_coeff_265 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 265 = (G * S0).coeff 265 := by
  rw [G_mul_coeff_ge S0 265 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_265, S0_coeff_264, S0_coeff_263, S0_coeff_262, S0_coeff_261, S0_coeff_260, S0_coeff_259, S0_coeff_258, S0_coeff_257, S0_coeff_256, S0_coeff_255, S0_coeff_254, S0_coeff_253]
  simp [G, T1]
  decide

lemma chain1_coeff_266 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 266 = (G * S0).coeff 266 := by
  rw [G_mul_coeff_ge S0 266 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_266, S0_coeff_265, S0_coeff_264, S0_coeff_263, S0_coeff_262, S0_coeff_261, S0_coeff_260, S0_coeff_259, S0_coeff_258, S0_coeff_257, S0_coeff_256, S0_coeff_255, S0_coeff_254]
  simp [G, T1]
  decide

lemma chain1_coeff_267 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 267 = (G * S0).coeff 267 := by
  rw [G_mul_coeff_ge S0 267 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_267, S0_coeff_266, S0_coeff_265, S0_coeff_264, S0_coeff_263, S0_coeff_262, S0_coeff_261, S0_coeff_260, S0_coeff_259, S0_coeff_258, S0_coeff_257, S0_coeff_256, S0_coeff_255]
  simp [G, T1]
  decide

lemma chain1_coeff_268 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 268 = (G * S0).coeff 268 := by
  rw [G_mul_coeff_ge S0 268 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_268, S0_coeff_267, S0_coeff_266, S0_coeff_265, S0_coeff_264, S0_coeff_263, S0_coeff_262, S0_coeff_261, S0_coeff_260, S0_coeff_259, S0_coeff_258, S0_coeff_257, S0_coeff_256]
  simp [G, T1]
  decide

lemma chain1_coeff_269 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 269 = (G * S0).coeff 269 := by
  rw [G_mul_coeff_ge S0 269 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_269, S0_coeff_268, S0_coeff_267, S0_coeff_266, S0_coeff_265, S0_coeff_264, S0_coeff_263, S0_coeff_262, S0_coeff_261, S0_coeff_260, S0_coeff_259, S0_coeff_258, S0_coeff_257]
  simp [G, T1]
  decide

lemma chain1_coeff_270 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 270 = (G * S0).coeff 270 := by
  rw [G_mul_coeff_ge S0 270 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_270, S0_coeff_269, S0_coeff_268, S0_coeff_267, S0_coeff_266, S0_coeff_265, S0_coeff_264, S0_coeff_263, S0_coeff_262, S0_coeff_261, S0_coeff_260, S0_coeff_259, S0_coeff_258]
  simp [G, T1]
  decide

lemma chain1_coeff_271 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 271 = (G * S0).coeff 271 := by
  rw [G_mul_coeff_ge S0 271 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_271, S0_coeff_270, S0_coeff_269, S0_coeff_268, S0_coeff_267, S0_coeff_266, S0_coeff_265, S0_coeff_264, S0_coeff_263, S0_coeff_262, S0_coeff_261, S0_coeff_260, S0_coeff_259]
  simp [G, T1]
  decide

lemma chain1_coeff_272 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 272 = (G * S0).coeff 272 := by
  rw [G_mul_coeff_ge S0 272 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_272, S0_coeff_271, S0_coeff_270, S0_coeff_269, S0_coeff_268, S0_coeff_267, S0_coeff_266, S0_coeff_265, S0_coeff_264, S0_coeff_263, S0_coeff_262, S0_coeff_261, S0_coeff_260]
  simp [G, T1]
  decide

lemma chain1_coeff_273 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 273 = (G * S0).coeff 273 := by
  rw [G_mul_coeff_ge S0 273 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_273, S0_coeff_272, S0_coeff_271, S0_coeff_270, S0_coeff_269, S0_coeff_268, S0_coeff_267, S0_coeff_266, S0_coeff_265, S0_coeff_264, S0_coeff_263, S0_coeff_262, S0_coeff_261]
  simp [G, T1]
  decide

lemma chain1_coeff_274 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 274 = (G * S0).coeff 274 := by
  rw [G_mul_coeff_ge S0 274 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_274, S0_coeff_273, S0_coeff_272, S0_coeff_271, S0_coeff_270, S0_coeff_269, S0_coeff_268, S0_coeff_267, S0_coeff_266, S0_coeff_265, S0_coeff_264, S0_coeff_263, S0_coeff_262]
  simp [G, T1]
  decide

lemma chain1_coeff_275 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 275 = (G * S0).coeff 275 := by
  rw [G_mul_coeff_ge S0 275 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_275, S0_coeff_274, S0_coeff_273, S0_coeff_272, S0_coeff_271, S0_coeff_270, S0_coeff_269, S0_coeff_268, S0_coeff_267, S0_coeff_266, S0_coeff_265, S0_coeff_264, S0_coeff_263]
  simp [G, T1]
  decide

lemma chain1_coeff_276 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 276 = (G * S0).coeff 276 := by
  rw [G_mul_coeff_ge S0 276 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_276, S0_coeff_275, S0_coeff_274, S0_coeff_273, S0_coeff_272, S0_coeff_271, S0_coeff_270, S0_coeff_269, S0_coeff_268, S0_coeff_267, S0_coeff_266, S0_coeff_265, S0_coeff_264]
  simp [G, T1]
  decide

lemma chain1_coeff_277 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 277 = (G * S0).coeff 277 := by
  rw [G_mul_coeff_ge S0 277 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_277, S0_coeff_276, S0_coeff_275, S0_coeff_274, S0_coeff_273, S0_coeff_272, S0_coeff_271, S0_coeff_270, S0_coeff_269, S0_coeff_268, S0_coeff_267, S0_coeff_266, S0_coeff_265]
  simp [G, T1]
  decide

lemma chain1_coeff_278 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 278 = (G * S0).coeff 278 := by
  rw [G_mul_coeff_ge S0 278 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_278, S0_coeff_277, S0_coeff_276, S0_coeff_275, S0_coeff_274, S0_coeff_273, S0_coeff_272, S0_coeff_271, S0_coeff_270, S0_coeff_269, S0_coeff_268, S0_coeff_267, S0_coeff_266]
  simp [G, T1]
  decide

lemma chain1_coeff_279 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 279 = (G * S0).coeff 279 := by
  rw [G_mul_coeff_ge S0 279 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_279, S0_coeff_278, S0_coeff_277, S0_coeff_276, S0_coeff_275, S0_coeff_274, S0_coeff_273, S0_coeff_272, S0_coeff_271, S0_coeff_270, S0_coeff_269, S0_coeff_268, S0_coeff_267]
  simp [G, T1]
  decide

lemma chain1_coeff_280 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 280 = (G * S0).coeff 280 := by
  rw [G_mul_coeff_ge S0 280 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_280, S0_coeff_279, S0_coeff_278, S0_coeff_277, S0_coeff_276, S0_coeff_275, S0_coeff_274, S0_coeff_273, S0_coeff_272, S0_coeff_271, S0_coeff_270, S0_coeff_269, S0_coeff_268]
  simp [G, T1]
  decide

lemma chain1_coeff_281 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 281 = (G * S0).coeff 281 := by
  rw [G_mul_coeff_ge S0 281 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_281, S0_coeff_280, S0_coeff_279, S0_coeff_278, S0_coeff_277, S0_coeff_276, S0_coeff_275, S0_coeff_274, S0_coeff_273, S0_coeff_272, S0_coeff_271, S0_coeff_270, S0_coeff_269]
  simp [G, T1]
  decide

lemma chain1_coeff_282 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 282 = (G * S0).coeff 282 := by
  rw [G_mul_coeff_ge S0 282 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_282, S0_coeff_281, S0_coeff_280, S0_coeff_279, S0_coeff_278, S0_coeff_277, S0_coeff_276, S0_coeff_275, S0_coeff_274, S0_coeff_273, S0_coeff_272, S0_coeff_271, S0_coeff_270]
  simp [G, T1]
  decide

lemma chain1_coeff_283 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 283 = (G * S0).coeff 283 := by
  rw [G_mul_coeff_ge S0 283 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_283, S0_coeff_282, S0_coeff_281, S0_coeff_280, S0_coeff_279, S0_coeff_278, S0_coeff_277, S0_coeff_276, S0_coeff_275, S0_coeff_274, S0_coeff_273, S0_coeff_272, S0_coeff_271]
  simp [G, T1]
  decide

lemma chain1_coeff_284 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 284 = (G * S0).coeff 284 := by
  rw [G_mul_coeff_ge S0 284 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_284, S0_coeff_283, S0_coeff_282, S0_coeff_281, S0_coeff_280, S0_coeff_279, S0_coeff_278, S0_coeff_277, S0_coeff_276, S0_coeff_275, S0_coeff_274, S0_coeff_273, S0_coeff_272]
  simp [G, T1]
  decide

lemma chain1_coeff_285 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 285 = (G * S0).coeff 285 := by
  rw [G_mul_coeff_ge S0 285 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_285, S0_coeff_284, S0_coeff_283, S0_coeff_282, S0_coeff_281, S0_coeff_280, S0_coeff_279, S0_coeff_278, S0_coeff_277, S0_coeff_276, S0_coeff_275, S0_coeff_274, S0_coeff_273]
  simp [G, T1]
  decide

lemma chain1_coeff_286 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 286 = (G * S0).coeff 286 := by
  rw [G_mul_coeff_ge S0 286 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_286, S0_coeff_285, S0_coeff_284, S0_coeff_283, S0_coeff_282, S0_coeff_281, S0_coeff_280, S0_coeff_279, S0_coeff_278, S0_coeff_277, S0_coeff_276, S0_coeff_275, S0_coeff_274]
  simp [G, T1]
  decide

lemma chain1_coeff_287 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 287 = (G * S0).coeff 287 := by
  rw [G_mul_coeff_ge S0 287 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_287, S0_coeff_286, S0_coeff_285, S0_coeff_284, S0_coeff_283, S0_coeff_282, S0_coeff_281, S0_coeff_280, S0_coeff_279, S0_coeff_278, S0_coeff_277, S0_coeff_276, S0_coeff_275]
  simp [G, T1]
  decide

lemma chain1_coeff_288 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 288 = (G * S0).coeff 288 := by
  rw [G_mul_coeff_ge S0 288 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_288, S0_coeff_287, S0_coeff_286, S0_coeff_285, S0_coeff_284, S0_coeff_283, S0_coeff_282, S0_coeff_281, S0_coeff_280, S0_coeff_279, S0_coeff_278, S0_coeff_277, S0_coeff_276]
  simp [G, T1]
  decide

lemma chain1_coeff_289 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 289 = (G * S0).coeff 289 := by
  rw [G_mul_coeff_ge S0 289 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_289, S0_coeff_288, S0_coeff_287, S0_coeff_286, S0_coeff_285, S0_coeff_284, S0_coeff_283, S0_coeff_282, S0_coeff_281, S0_coeff_280, S0_coeff_279, S0_coeff_278, S0_coeff_277]
  simp [G, T1]
  decide

lemma chain1_coeff_290 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 290 = (G * S0).coeff 290 := by
  rw [G_mul_coeff_ge S0 290 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_290, S0_coeff_289, S0_coeff_288, S0_coeff_287, S0_coeff_286, S0_coeff_285, S0_coeff_284, S0_coeff_283, S0_coeff_282, S0_coeff_281, S0_coeff_280, S0_coeff_279, S0_coeff_278]
  simp [G, T1]
  decide

lemma chain1_coeff_291 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 291 = (G * S0).coeff 291 := by
  rw [G_mul_coeff_ge S0 291 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_291, S0_coeff_290, S0_coeff_289, S0_coeff_288, S0_coeff_287, S0_coeff_286, S0_coeff_285, S0_coeff_284, S0_coeff_283, S0_coeff_282, S0_coeff_281, S0_coeff_280, S0_coeff_279]
  simp [G, T1]
  decide

lemma chain1_coeff_292 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 292 = (G * S0).coeff 292 := by
  rw [G_mul_coeff_ge S0 292 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_292, S0_coeff_291, S0_coeff_290, S0_coeff_289, S0_coeff_288, S0_coeff_287, S0_coeff_286, S0_coeff_285, S0_coeff_284, S0_coeff_283, S0_coeff_282, S0_coeff_281, S0_coeff_280]
  simp [G, T1]
  decide

lemma chain1_coeff_293 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 293 = (G * S0).coeff 293 := by
  rw [G_mul_coeff_ge S0 293 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_293, S0_coeff_292, S0_coeff_291, S0_coeff_290, S0_coeff_289, S0_coeff_288, S0_coeff_287, S0_coeff_286, S0_coeff_285, S0_coeff_284, S0_coeff_283, S0_coeff_282, S0_coeff_281]
  simp [G, T1]
  decide

lemma chain1_coeff_294 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 294 = (G * S0).coeff 294 := by
  rw [G_mul_coeff_ge S0 294 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_294, S0_coeff_293, S0_coeff_292, S0_coeff_291, S0_coeff_290, S0_coeff_289, S0_coeff_288, S0_coeff_287, S0_coeff_286, S0_coeff_285, S0_coeff_284, S0_coeff_283, S0_coeff_282]
  simp [G, T1]
  decide

lemma chain1_coeff_295 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 295 = (G * S0).coeff 295 := by
  rw [G_mul_coeff_ge S0 295 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_295, S0_coeff_294, S0_coeff_293, S0_coeff_292, S0_coeff_291, S0_coeff_290, S0_coeff_289, S0_coeff_288, S0_coeff_287, S0_coeff_286, S0_coeff_285, S0_coeff_284, S0_coeff_283]
  simp [G, T1]
  decide

lemma chain1_coeff_296 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 296 = (G * S0).coeff 296 := by
  rw [G_mul_coeff_ge S0 296 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_296, S0_coeff_295, S0_coeff_294, S0_coeff_293, S0_coeff_292, S0_coeff_291, S0_coeff_290, S0_coeff_289, S0_coeff_288, S0_coeff_287, S0_coeff_286, S0_coeff_285, S0_coeff_284]
  simp [G, T1]
  decide

lemma chain1_coeff_297 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 297 = (G * S0).coeff 297 := by
  rw [G_mul_coeff_ge S0 297 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_297, S0_coeff_296, S0_coeff_295, S0_coeff_294, S0_coeff_293, S0_coeff_292, S0_coeff_291, S0_coeff_290, S0_coeff_289, S0_coeff_288, S0_coeff_287, S0_coeff_286, S0_coeff_285]
  simp [G, T1]
  decide

lemma chain1_coeff_298 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 298 = (G * S0).coeff 298 := by
  rw [G_mul_coeff_ge S0 298 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_298, S0_coeff_297, S0_coeff_296, S0_coeff_295, S0_coeff_294, S0_coeff_293, S0_coeff_292, S0_coeff_291, S0_coeff_290, S0_coeff_289, S0_coeff_288, S0_coeff_287, S0_coeff_286]
  simp [G, T1]
  decide

lemma chain1_coeff_299 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 299 = (G * S0).coeff 299 := by
  rw [G_mul_coeff_ge S0 299 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_299, S0_coeff_298, S0_coeff_297, S0_coeff_296, S0_coeff_295, S0_coeff_294, S0_coeff_293, S0_coeff_292, S0_coeff_291, S0_coeff_290, S0_coeff_289, S0_coeff_288, S0_coeff_287]
  simp [G, T1]
  decide

lemma chain1_coeff_300 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 300 = (G * S0).coeff 300 := by
  rw [G_mul_coeff_ge S0 300 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_300, S0_coeff_299, S0_coeff_298, S0_coeff_297, S0_coeff_296, S0_coeff_295, S0_coeff_294, S0_coeff_293, S0_coeff_292, S0_coeff_291, S0_coeff_290, S0_coeff_289, S0_coeff_288]
  simp [G, T1]
  decide

lemma chain1_coeff_301 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 301 = (G * S0).coeff 301 := by
  rw [G_mul_coeff_ge S0 301 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_301, S0_coeff_300, S0_coeff_299, S0_coeff_298, S0_coeff_297, S0_coeff_296, S0_coeff_295, S0_coeff_294, S0_coeff_293, S0_coeff_292, S0_coeff_291, S0_coeff_290, S0_coeff_289]
  simp [G, T1]
  decide

lemma chain1_coeff_302 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 302 = (G * S0).coeff 302 := by
  rw [G_mul_coeff_ge S0 302 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_302, S0_coeff_301, S0_coeff_300, S0_coeff_299, S0_coeff_298, S0_coeff_297, S0_coeff_296, S0_coeff_295, S0_coeff_294, S0_coeff_293, S0_coeff_292, S0_coeff_291, S0_coeff_290]
  simp [G, T1]
  decide

lemma chain1_coeff_303 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 303 = (G * S0).coeff 303 := by
  rw [G_mul_coeff_ge S0 303 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_303, S0_coeff_302, S0_coeff_301, S0_coeff_300, S0_coeff_299, S0_coeff_298, S0_coeff_297, S0_coeff_296, S0_coeff_295, S0_coeff_294, S0_coeff_293, S0_coeff_292, S0_coeff_291]
  simp [G, T1]
  decide

lemma chain1_coeff_304 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 304 = (G * S0).coeff 304 := by
  rw [G_mul_coeff_ge S0 304 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_304, S0_coeff_303, S0_coeff_302, S0_coeff_301, S0_coeff_300, S0_coeff_299, S0_coeff_298, S0_coeff_297, S0_coeff_296, S0_coeff_295, S0_coeff_294, S0_coeff_293, S0_coeff_292]
  simp [G, T1]
  decide

lemma chain1_coeff_305 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 305 = (G * S0).coeff 305 := by
  rw [G_mul_coeff_ge S0 305 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_305, S0_coeff_304, S0_coeff_303, S0_coeff_302, S0_coeff_301, S0_coeff_300, S0_coeff_299, S0_coeff_298, S0_coeff_297, S0_coeff_296, S0_coeff_295, S0_coeff_294, S0_coeff_293]
  simp [G, T1]
  decide

lemma chain1_coeff_306 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 306 = (G * S0).coeff 306 := by
  rw [G_mul_coeff_ge S0 306 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_306, S0_coeff_305, S0_coeff_304, S0_coeff_303, S0_coeff_302, S0_coeff_301, S0_coeff_300, S0_coeff_299, S0_coeff_298, S0_coeff_297, S0_coeff_296, S0_coeff_295, S0_coeff_294]
  simp [G, T1]
  decide

lemma chain1_coeff_307 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 307 = (G * S0).coeff 307 := by
  rw [G_mul_coeff_ge S0 307 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_307, S0_coeff_306, S0_coeff_305, S0_coeff_304, S0_coeff_303, S0_coeff_302, S0_coeff_301, S0_coeff_300, S0_coeff_299, S0_coeff_298, S0_coeff_297, S0_coeff_296, S0_coeff_295]
  simp [G, T1]
  decide

lemma chain1_coeff_308 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 308 = (G * S0).coeff 308 := by
  rw [G_mul_coeff_ge S0 308 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_308, S0_coeff_307, S0_coeff_306, S0_coeff_305, S0_coeff_304, S0_coeff_303, S0_coeff_302, S0_coeff_301, S0_coeff_300, S0_coeff_299, S0_coeff_298, S0_coeff_297, S0_coeff_296]
  simp [G, T1]
  decide

lemma chain1_coeff_309 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 309 = (G * S0).coeff 309 := by
  rw [G_mul_coeff_ge S0 309 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_309, S0_coeff_308, S0_coeff_307, S0_coeff_306, S0_coeff_305, S0_coeff_304, S0_coeff_303, S0_coeff_302, S0_coeff_301, S0_coeff_300, S0_coeff_299, S0_coeff_298, S0_coeff_297]
  simp [G, T1]
  decide

lemma chain1_coeff_310 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 310 = (G * S0).coeff 310 := by
  rw [G_mul_coeff_ge S0 310 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_310, S0_coeff_309, S0_coeff_308, S0_coeff_307, S0_coeff_306, S0_coeff_305, S0_coeff_304, S0_coeff_303, S0_coeff_302, S0_coeff_301, S0_coeff_300, S0_coeff_299, S0_coeff_298]
  simp [G, T1]
  decide

lemma chain1_coeff_311 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 311 = (G * S0).coeff 311 := by
  rw [G_mul_coeff_ge S0 311 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_311, S0_coeff_310, S0_coeff_309, S0_coeff_308, S0_coeff_307, S0_coeff_306, S0_coeff_305, S0_coeff_304, S0_coeff_303, S0_coeff_302, S0_coeff_301, S0_coeff_300, S0_coeff_299]
  simp [G, T1]
  decide

lemma chain1_coeff_312 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 312 = (G * S0).coeff 312 := by
  rw [G_mul_coeff_ge S0 312 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_312, S0_coeff_311, S0_coeff_310, S0_coeff_309, S0_coeff_308, S0_coeff_307, S0_coeff_306, S0_coeff_305, S0_coeff_304, S0_coeff_303, S0_coeff_302, S0_coeff_301, S0_coeff_300]
  simp [G, T1]
  decide

lemma chain1_coeff_313 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 313 = (G * S0).coeff 313 := by
  rw [G_mul_coeff_ge S0 313 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_313, S0_coeff_312, S0_coeff_311, S0_coeff_310, S0_coeff_309, S0_coeff_308, S0_coeff_307, S0_coeff_306, S0_coeff_305, S0_coeff_304, S0_coeff_303, S0_coeff_302, S0_coeff_301]
  simp [G, T1]
  decide

lemma chain1_coeff_314 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 314 = (G * S0).coeff 314 := by
  rw [G_mul_coeff_ge S0 314 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_314, S0_coeff_313, S0_coeff_312, S0_coeff_311, S0_coeff_310, S0_coeff_309, S0_coeff_308, S0_coeff_307, S0_coeff_306, S0_coeff_305, S0_coeff_304, S0_coeff_303, S0_coeff_302]
  simp [G, T1]
  decide

lemma chain1_coeff_315 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 315 = (G * S0).coeff 315 := by
  rw [G_mul_coeff_ge S0 315 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_315, S0_coeff_314, S0_coeff_313, S0_coeff_312, S0_coeff_311, S0_coeff_310, S0_coeff_309, S0_coeff_308, S0_coeff_307, S0_coeff_306, S0_coeff_305, S0_coeff_304, S0_coeff_303]
  simp [G, T1]
  decide

lemma chain1_coeff_316 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 316 = (G * S0).coeff 316 := by
  rw [G_mul_coeff_ge S0 316 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_316, S0_coeff_315, S0_coeff_314, S0_coeff_313, S0_coeff_312, S0_coeff_311, S0_coeff_310, S0_coeff_309, S0_coeff_308, S0_coeff_307, S0_coeff_306, S0_coeff_305, S0_coeff_304]
  simp [G, T1]
  decide

lemma chain1_coeff_317 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 317 = (G * S0).coeff 317 := by
  rw [G_mul_coeff_ge S0 317 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_317, S0_coeff_316, S0_coeff_315, S0_coeff_314, S0_coeff_313, S0_coeff_312, S0_coeff_311, S0_coeff_310, S0_coeff_309, S0_coeff_308, S0_coeff_307, S0_coeff_306, S0_coeff_305]
  simp [G, T1]
  decide

lemma chain1_coeff_318 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 318 = (G * S0).coeff 318 := by
  rw [G_mul_coeff_ge S0 318 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_318, S0_coeff_317, S0_coeff_316, S0_coeff_315, S0_coeff_314, S0_coeff_313, S0_coeff_312, S0_coeff_311, S0_coeff_310, S0_coeff_309, S0_coeff_308, S0_coeff_307, S0_coeff_306]
  simp [G, T1]
  decide

lemma chain1_coeff_319 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 319 = (G * S0).coeff 319 := by
  rw [G_mul_coeff_ge S0 319 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_319, S0_coeff_318, S0_coeff_317, S0_coeff_316, S0_coeff_315, S0_coeff_314, S0_coeff_313, S0_coeff_312, S0_coeff_311, S0_coeff_310, S0_coeff_309, S0_coeff_308, S0_coeff_307]
  simp [G, T1]
  decide

lemma chain1_coeff_320 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 320 = (G * S0).coeff 320 := by
  rw [G_mul_coeff_ge S0 320 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_320, S0_coeff_319, S0_coeff_318, S0_coeff_317, S0_coeff_316, S0_coeff_315, S0_coeff_314, S0_coeff_313, S0_coeff_312, S0_coeff_311, S0_coeff_310, S0_coeff_309, S0_coeff_308]
  simp [G, T1]
  decide

end LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual

end
