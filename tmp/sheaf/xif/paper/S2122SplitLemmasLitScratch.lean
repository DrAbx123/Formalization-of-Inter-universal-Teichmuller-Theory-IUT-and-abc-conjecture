import tmp.sheaf.xif.paper.S2094Mod29IrreducibleActual

open Polynomial
local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace S2122Mod29Split

instance instCharP : CharP (AdjoinRoot f) 29 := by
  have hdeg0 : f.degree ≠ 0 := by
    rw [degree_eq_natDegree hfmonic.ne_zero, hfdeg]
    norm_num
  have hinj : Function.Injective (algebraMap (ZMod 29) (AdjoinRoot f)) := by
    rw [AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.of.injective_of_degree_ne_zero hdeg0
  exact charP_of_injective_algebraMap hinj 29

lemma hpow1 (x : AdjoinRoot f) (hx : aeval x f = 0) :
    x ^ (29 ^ 1) = aeval x P1 := by
  have h : aeval x ((X : (ZMod 29)[X]) ^ 29 - P1) = 0 := by
    rw [cert_P1]
    simp [AdjoinRoot.aeval_eq, hx]
  have h' : x ^ 29 - aeval x P1 = 0 := by simpa using h
  simpa [pow_one] using sub_eq_zero.mp h'

lemma hR0 (x : AdjoinRoot f) : (aeval x P1)^0 = aeval x (Rfun 0) := by
  simp [Rfun, R0]

lemma hR1 (x : AdjoinRoot f) : (aeval x P1)^1 = aeval x (Rfun 1) := by
  simp [Rfun, R1, P1]

lemma hR2 (x : AdjoinRoot f) (hx : aeval x f = 0) :
    (aeval x P1)^2 = aeval x (Rfun 2) := by
  have h : aeval x (R1 * P1 - R2) = 0 := by
    rw [cert_R2]
    simp [AdjoinRoot.aeval_eq, hx]
  have h' : aeval x (R1 * P1) = aeval x R2 := by
    have h2 : aeval x (R1 * P1) - aeval x R2 = 0 := by simpa using h
    exact sub_eq_zero.mp h2
  calc
    (aeval x P1)^2 = (aeval x P1)^1 * aeval x P1 := by
      rw [show 2 = 1 + 1 by norm_num, pow_succ]
    _ = aeval x R1 * aeval x P1 := by
      rw [hR1 x]
      simp [Rfun, R1]
    _ = aeval x (R1 * P1) := by rw [map_mul]
    _ = aeval x R2 := h'
    _ = aeval x (Rfun 2) := by simp [Rfun, R2]

lemma hR3 (x : AdjoinRoot f) (hx : aeval x f = 0) :
    (aeval x P1)^3 = aeval x (Rfun 3) := by
  have h : aeval x (R2 * P1 - R3) = 0 := by
    rw [cert_R3]
    simp [AdjoinRoot.aeval_eq, hx]
  have h' : aeval x (R2 * P1) = aeval x R3 := by
    have h2 : aeval x (R2 * P1) - aeval x R3 = 0 := by simpa using h
    exact sub_eq_zero.mp h2
  calc
    (aeval x P1)^3 = (aeval x P1)^2 * aeval x P1 := by
      rw [show 3 = 2 + 1 by norm_num, pow_succ]
    _ = aeval x R2 * aeval x P1 := by
      rw [hR2 x hx]
      simp [Rfun, R2]
    _ = aeval x (R2 * P1) := by rw [map_mul]
    _ = aeval x R3 := h'
    _ = aeval x (Rfun 3) := by simp [Rfun, R3]

lemma hR4 (x : AdjoinRoot f) (hx : aeval x f = 0) :
    (aeval x P1)^4 = aeval x (Rfun 4) := by
  have h : aeval x (R3 * P1 - R4) = 0 := by
    rw [cert_R4]
    simp [AdjoinRoot.aeval_eq, hx]
  have h' : aeval x (R3 * P1) = aeval x R4 := by
    have h2 : aeval x (R3 * P1) - aeval x R4 = 0 := by simpa using h
    exact sub_eq_zero.mp h2
  calc
    (aeval x P1)^4 = (aeval x P1)^3 * aeval x P1 := by
      rw [show 4 = 3 + 1 by norm_num, pow_succ]
    _ = aeval x R3 * aeval x P1 := by
      rw [hR3 x hx]
      simp [Rfun, R3]
    _ = aeval x (R3 * P1) := by rw [map_mul]
    _ = aeval x R4 := h'
    _ = aeval x (Rfun 4) := by simp [Rfun, R4]

lemma hR5 (x : AdjoinRoot f) (hx : aeval x f = 0) :
    (aeval x P1)^5 = aeval x (Rfun 5) := by
  have h : aeval x (R4 * P1 - R5) = 0 := by
    rw [cert_R5]
    simp [AdjoinRoot.aeval_eq, hx]
  have h' : aeval x (R4 * P1) = aeval x R5 := by
    have h2 : aeval x (R4 * P1) - aeval x R5 = 0 := by simpa using h
    exact sub_eq_zero.mp h2
  calc
    (aeval x P1)^5 = (aeval x P1)^4 * aeval x P1 := by
      rw [show 5 = 4 + 1 by norm_num, pow_succ]
    _ = aeval x R4 * aeval x P1 := by
      rw [hR4 x hx]
      simp [Rfun, R4]
    _ = aeval x (R4 * P1) := by rw [map_mul]
    _ = aeval x R5 := h'
    _ = aeval x (Rfun 5) := by simp [Rfun, R5]

lemma hR6 (x : AdjoinRoot f) (hx : aeval x f = 0) :
    (aeval x P1)^6 = aeval x (Rfun 6) := by
  have h : aeval x (R5 * P1 - R6) = 0 := by
    rw [cert_R6]
    simp [AdjoinRoot.aeval_eq, hx]
  have h' : aeval x (R5 * P1) = aeval x R6 := by
    have h2 : aeval x (R5 * P1) - aeval x R6 = 0 := by simpa using h
    exact sub_eq_zero.mp h2
  calc
    (aeval x P1)^6 = (aeval x P1)^5 * aeval x P1 := by
      rw [show 6 = 5 + 1 by norm_num, pow_succ]
    _ = aeval x R5 * aeval x P1 := by
      rw [hR5 x hx]
      simp [Rfun, R5]
    _ = aeval x (R5 * P1) := by rw [map_mul]
    _ = aeval x R6 := h'
    _ = aeval x (Rfun 6) := by simp [Rfun, R6]

lemma hR7 (x : AdjoinRoot f) (hx : aeval x f = 0) :
    (aeval x P1)^7 = aeval x (Rfun 7) := by
  have h : aeval x (R6 * P1 - R7) = 0 := by
    rw [cert_R7]
    simp [AdjoinRoot.aeval_eq, hx]
  have h' : aeval x (R6 * P1) = aeval x R7 := by
    have h2 : aeval x (R6 * P1) - aeval x R7 = 0 := by simpa using h
    exact sub_eq_zero.mp h2
  calc
    (aeval x P1)^7 = (aeval x P1)^6 * aeval x P1 := by
      rw [show 7 = 6 + 1 by norm_num, pow_succ]
    _ = aeval x R6 * aeval x P1 := by
      rw [hR6 x hx]
      simp [Rfun, R6]
    _ = aeval x (R6 * P1) := by rw [map_mul]
    _ = aeval x R7 := h'
    _ = aeval x (Rfun 7) := by simp [Rfun, R7]

lemma hR8 (x : AdjoinRoot f) (hx : aeval x f = 0) :
    (aeval x P1)^8 = aeval x (Rfun 8) := by
  have h : aeval x (R7 * P1 - R8) = 0 := by
    rw [cert_R8]
    simp [AdjoinRoot.aeval_eq, hx]
  have h' : aeval x (R7 * P1) = aeval x R8 := by
    have h2 : aeval x (R7 * P1) - aeval x R8 = 0 := by simpa using h
    exact sub_eq_zero.mp h2
  calc
    (aeval x P1)^8 = (aeval x P1)^7 * aeval x P1 := by
      rw [show 8 = 7 + 1 by norm_num, pow_succ]
    _ = aeval x R7 * aeval x P1 := by
      rw [hR7 x hx]
      simp [Rfun, R7]
    _ = aeval x (R7 * P1) := by rw [map_mul]
    _ = aeval x R8 := h'
    _ = aeval x (Rfun 8) := by simp [Rfun, R8]

lemma hR9 (x : AdjoinRoot f) (hx : aeval x f = 0) :
    (aeval x P1)^9 = aeval x (Rfun 9) := by
  have h : aeval x (R8 * P1 - R9) = 0 := by
    rw [cert_R9]
    simp [AdjoinRoot.aeval_eq, hx]
  have h' : aeval x (R8 * P1) = aeval x R9 := by
    have h2 : aeval x (R8 * P1) - aeval x R9 = 0 := by simpa using h
    exact sub_eq_zero.mp h2
  calc
    (aeval x P1)^9 = (aeval x P1)^8 * aeval x P1 := by
      rw [show 9 = 8 + 1 by norm_num, pow_succ]
    _ = aeval x R8 * aeval x P1 := by
      rw [hR8 x hx]
      simp [Rfun, R8]
    _ = aeval x (R8 * P1) := by rw [map_mul]
    _ = aeval x R9 := h'
    _ = aeval x (Rfun 9) := by simp [Rfun, R9]

lemma hRpow (x : AdjoinRoot f) (hx : aeval x f = 0) :
    ∀ j, j < 10 → (aeval x P1)^j = aeval x (Rfun j) := by
  intro j hj
  interval_cases j
  · exact hR0 x
  · exact hR1 x
  · exact hR2 x hx
  · exact hR3 x hx
  · exact hR4 x hx
  · exact hR5 x hx
  · exact hR6 x hx
  · exact hR7 x hx
  · exact hR8 x hx
  · exact hR9 x hx

lemma hpow2 (x : AdjoinRoot f) (hx : aeval x f = 0) :
    x ^ (29 ^ 2) = aeval x P2 := by
  calc
    x ^ (29 ^ 2) = (x ^ (29 ^ 1)) ^ 29 := by
      rw [show 29 ^ 2 = 29 ^ 1 * 29 by norm_num, pow_mul]
    _ = (aeval x P1) ^ 29 := by rw [hpow1 x hx]
    _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P1).coeff j) * (x ^ 29) ^ j :=
        aeval_pow_char_29 x hP1deg
    _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P1).coeff j) * (aeval x P1) ^ j := by
        rw [show x ^ 29 = aeval x P1 by simpa [pow_one] using hpow1 x hx]
    _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P1).coeff j) * aeval x (Rfun j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hRpow x hx j (by simpa using hj)]
    _ = aeval x (∑ j ∈ Finset.range 10, C ((P1).coeff j) * Rfun j) := by
        simp [map_sum, map_mul, aeval_C]
    _ = aeval x P2 := by rw [hlin1']

lemma hpow3 (x : AdjoinRoot f) (hx : aeval x f = 0) :
    x ^ (29 ^ 3) = aeval x P3 := by
  calc
    x ^ (29 ^ 3) = (x ^ (29 ^ 2)) ^ 29 := by
      rw [show 29 ^ 3 = 29 ^ 2 * 29 by norm_num, pow_mul]
    _ = (aeval x P2) ^ 29 := by rw [hpow2 x hx]
    _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P2).coeff j) * (x ^ 29) ^ j :=
        aeval_pow_char_29 x hP2deg
    _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P2).coeff j) * (aeval x P1) ^ j := by
        rw [show x ^ 29 = aeval x P1 by simpa [pow_one] using hpow1 x hx]
    _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P2).coeff j) * aeval x (Rfun j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hRpow x hx j (by simpa using hj)]
    _ = aeval x (∑ j ∈ Finset.range 10, C ((P2).coeff j) * Rfun j) := by
        simp [map_sum, map_mul, aeval_C]
    _ = aeval x P3 := by rw [hlin2']

lemma hpow4 (x : AdjoinRoot f) (hx : aeval x f = 0) :
    x ^ (29 ^ 4) = aeval x P4 := by
  calc
    x ^ (29 ^ 4) = (x ^ (29 ^ 3)) ^ 29 := by
      rw [show 29 ^ 4 = 29 ^ 3 * 29 by norm_num, pow_mul]
    _ = (aeval x P3) ^ 29 := by rw [hpow3 x hx]
    _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P3).coeff j) * (x ^ 29) ^ j :=
        aeval_pow_char_29 x hP3deg
    _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P3).coeff j) * (aeval x P1) ^ j := by
        rw [show x ^ 29 = aeval x P1 by simpa [pow_one] using hpow1 x hx]
    _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P3).coeff j) * aeval x (Rfun j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hRpow x hx j (by simpa using hj)]
    _ = aeval x (∑ j ∈ Finset.range 10, C ((P3).coeff j) * Rfun j) := by
        simp [map_sum, map_mul, aeval_C]
    _ = aeval x P4 := by rw [hlin3']

lemma hpow5 (x : AdjoinRoot f) (hx : aeval x f = 0) :
    x ^ (29 ^ 5) = aeval x P5 := by
  calc
    x ^ (29 ^ 5) = (x ^ (29 ^ 4)) ^ 29 := by
      rw [show 29 ^ 5 = 29 ^ 4 * 29 by norm_num, pow_mul]
    _ = (aeval x P4) ^ 29 := by rw [hpow4 x hx]
    _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P4).coeff j) * (x ^ 29) ^ j :=
        aeval_pow_char_29 x hP4deg
    _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P4).coeff j) * (aeval x P1) ^ j := by
        rw [show x ^ 29 = aeval x P1 by simpa [pow_one] using hpow1 x hx]
    _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P4).coeff j) * aeval x (Rfun j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hRpow x hx j (by simpa using hj)]
    _ = aeval x (∑ j ∈ Finset.range 10, C ((P4).coeff j) * Rfun j) := by
        simp [map_sum, map_mul, aeval_C]
    _ = aeval x P5 := by rw [hlin4']

lemma hpow6 (x : AdjoinRoot f) (hx : aeval x f = 0) :
    x ^ (29 ^ 6) = aeval x P6 := by
  calc
    x ^ (29 ^ 6) = (x ^ (29 ^ 5)) ^ 29 := by
      rw [show 29 ^ 6 = 29 ^ 5 * 29 by norm_num, pow_mul]
    _ = (aeval x P5) ^ 29 := by rw [hpow5 x hx]
    _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P5).coeff j) * (x ^ 29) ^ j :=
        aeval_pow_char_29 x hP5deg
    _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P5).coeff j) * (aeval x P1) ^ j := by
        rw [show x ^ 29 = aeval x P1 by simpa [pow_one] using hpow1 x hx]
    _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P5).coeff j) * aeval x (Rfun j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hRpow x hx j (by simpa using hj)]
    _ = aeval x (∑ j ∈ Finset.range 10, C ((P5).coeff j) * Rfun j) := by
        simp [map_sum, map_mul, aeval_C]
    _ = aeval x P6 := by rw [hlin5']

lemma hpow7 (x : AdjoinRoot f) (hx : aeval x f = 0) :
    x ^ (29 ^ 7) = aeval x P7 := by
  calc
    x ^ (29 ^ 7) = (x ^ (29 ^ 6)) ^ 29 := by
      rw [show 29 ^ 7 = 29 ^ 6 * 29 by norm_num, pow_mul]
    _ = (aeval x P6) ^ 29 := by rw [hpow6 x hx]
    _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P6).coeff j) * (x ^ 29) ^ j :=
        aeval_pow_char_29 x hP6deg
    _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P6).coeff j) * (aeval x P1) ^ j := by
        rw [show x ^ 29 = aeval x P1 by simpa [pow_one] using hpow1 x hx]
    _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P6).coeff j) * aeval x (Rfun j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hRpow x hx j (by simpa using hj)]
    _ = aeval x (∑ j ∈ Finset.range 10, C ((P6).coeff j) * Rfun j) := by
        simp [map_sum, map_mul, aeval_C]
    _ = aeval x P7 := by rw [hlin6']

lemma hpow8 (x : AdjoinRoot f) (hx : aeval x f = 0) :
    x ^ (29 ^ 8) = aeval x P8 := by
  calc
    x ^ (29 ^ 8) = (x ^ (29 ^ 7)) ^ 29 := by
      rw [show 29 ^ 8 = 29 ^ 7 * 29 by norm_num, pow_mul]
    _ = (aeval x P7) ^ 29 := by rw [hpow7 x hx]
    _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P7).coeff j) * (x ^ 29) ^ j :=
        aeval_pow_char_29 x hP7deg
    _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P7).coeff j) * (aeval x P1) ^ j := by
        rw [show x ^ 29 = aeval x P1 by simpa [pow_one] using hpow1 x hx]
    _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P7).coeff j) * aeval x (Rfun j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hRpow x hx j (by simpa using hj)]
    _ = aeval x (∑ j ∈ Finset.range 10, C ((P7).coeff j) * Rfun j) := by
        simp [map_sum, map_mul, aeval_C]
    _ = aeval x P8 := by rw [hlin7']

lemma hpow9 (x : AdjoinRoot f) (hx : aeval x f = 0) :
    x ^ (29 ^ 9) = aeval x P9 := by
  calc
    x ^ (29 ^ 9) = (x ^ (29 ^ 8)) ^ 29 := by
      rw [show 29 ^ 9 = 29 ^ 8 * 29 by norm_num, pow_mul]
    _ = (aeval x P8) ^ 29 := by rw [hpow8 x hx]
    _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P8).coeff j) * (x ^ 29) ^ j :=
        aeval_pow_char_29 x hP8deg
    _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P8).coeff j) * (aeval x P1) ^ j := by
        rw [show x ^ 29 = aeval x P1 by simpa [pow_one] using hpow1 x hx]
    _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P8).coeff j) * aeval x (Rfun j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hRpow x hx j (by simpa using hj)]
    _ = aeval x (∑ j ∈ Finset.range 10, C ((P8).coeff j) * Rfun j) := by
        simp [map_sum, map_mul, aeval_C]
    _ = aeval x P9 := by rw [hlin8']

lemma hpow10 (x : AdjoinRoot f) (hx : aeval x f = 0) :
    x ^ (29 ^ 10) = aeval x P10 := by
  calc
    x ^ (29 ^ 10) = (x ^ (29 ^ 9)) ^ 29 := by
      rw [show 29 ^ 10 = 29 ^ 9 * 29 by norm_num, pow_mul]
    _ = (aeval x P9) ^ 29 := by rw [hpow9 x hx]
    _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P9).coeff j) * (x ^ 29) ^ j :=
        aeval_pow_char_29 x hP9deg
    _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P9).coeff j) * (aeval x P1) ^ j := by
        rw [show x ^ 29 = aeval x P1 by simpa [pow_one] using hpow1 x hx]
    _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P9).coeff j) * aeval x (Rfun j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hRpow x hx j (by simpa using hj)]
    _ = aeval x (∑ j ∈ Finset.range 10, C ((P9).coeff j) * Rfun j) := by
        simp [map_sum, map_mul, aeval_C]
    _ = aeval x P10 := by rw [hlin9']

lemma root_aeval_f : aeval (AdjoinRoot.root f) f = 0 := by
  rw [AdjoinRoot.aeval_eq]
  exact AdjoinRoot.mk_self

lemma hpow2_lit (x : AdjoinRoot f) (hx : aeval x f = 0) :
    x ^ 841 = aeval x P2 := by
  have h : (29 : ℕ) ^ 2 = 841 := by norm_num
  rw [← h]
  exact hpow2 x hx

lemma hpow5_lit (x : AdjoinRoot f) (hx : aeval x f = 0) :
    x ^ 20511149 = aeval x P5 := by
  have h : (29 : ℕ) ^ 5 = 20511149 := by norm_num
  rw [← h]
  exact hpow5 x hx

lemma hpow10_lit (x : AdjoinRoot f) (hx : aeval x f = 0) :
    x ^ 420707233300201 = aeval x P10 := by
  have h : (29 : ℕ) ^ 10 = 420707233300201 := by norm_num
  rw [← h]
  exact hpow10 x hx

lemma hpow10x_root_lit : (AdjoinRoot.root f) ^ 420707233300201 = AdjoinRoot.root f := by
  rw [hpow10_lit (AdjoinRoot.root f) root_aeval_f]
  simp [P10]

lemma hdvd_lit : f ∣ (X : (ZMod 29)[X]) ^ 420707233300201 - X := by
  rw [← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.aeval_eq]
  have hmain : aeval (AdjoinRoot.root f) ((X : (ZMod 29)[X]) ^ 420707233300201 - X) =
      (AdjoinRoot.root f) ^ 420707233300201 - AdjoinRoot.root f := by
    simp [map_sub, map_pow, aeval_X]
  rw [hmain, hpow10x_root_lit, sub_self]

lemma hdiv2_lit : f ∣ (X : (ZMod 29)[X]) ^ 841 - P2 := by
  rw [← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.aeval_eq]
  have hmain : aeval (AdjoinRoot.root f) ((X : (ZMod 29)[X]) ^ 841 - P2) =
      (AdjoinRoot.root f) ^ 841 - aeval (AdjoinRoot.root f) P2 := by
    simp [map_sub, map_pow, aeval_X]
  rw [hmain, hpow2_lit (AdjoinRoot.root f) root_aeval_f, sub_self]

lemma hcop2 : IsCoprime f (P2 - X) := by
  refine ⟨A2, B2, ?_⟩
  rw [← hG2]
  exact cert_bez2

lemma h2_lit : IsCoprime f ((X : (ZMod 29)[X]) ^ 841 - X) := by
  rcases hdiv2_lit with ⟨q2, hq2⟩
  have hEq : (X : (ZMod 29)[X]) ^ 841 - X = (P2 - X) + f * q2 := by
    rw [← hq2]
    abel
  rw [hEq]
  exact hcop2.add_mul_left_right q2

lemma hdiv5_lit : f ∣ (X : (ZMod 29)[X]) ^ 20511149 - P5 := by
  rw [← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.aeval_eq]
  have hmain : aeval (AdjoinRoot.root f) ((X : (ZMod 29)[X]) ^ 20511149 - P5) =
      (AdjoinRoot.root f) ^ 20511149 - aeval (AdjoinRoot.root f) P5 := by
    simp [map_sub, map_pow, aeval_X]
  rw [hmain, hpow5_lit (AdjoinRoot.root f) root_aeval_f, sub_self]

lemma hcop5 : IsCoprime f (P5 - X) := by
  refine ⟨A5, B5, ?_⟩
  rw [← hG5]
  exact cert_bez5

lemma h5_lit : IsCoprime f ((X : (ZMod 29)[X]) ^ 20511149 - X) := by
  rcases hdiv5_lit with ⟨q5, hq5⟩
  have hEq : (X : (ZMod 29)[X]) ^ 20511149 - X = (P5 - X) + f * q5 := by
    rw [← hq5]
    abel
  rw [hEq]
  exact hcop5.add_mul_left_right q5

lemma natCard_zmod_29 : Nat.card (ZMod 29) = 29 := Nat.card_zmod 29

lemma natCard_pow10 : (Nat.card (ZMod 29)) ^ 10 = 420707233300201 := by
  rw [natCard_zmod_29]
  norm_num

lemma natCard_pow2 : (Nat.card (ZMod 29)) ^ 2 = 841 := by
  rw [natCard_zmod_29]
  norm_num

lemma natCard_pow5 : (Nat.card (ZMod 29)) ^ 5 = 20511149 := by
  rw [natCard_zmod_29]
  norm_num

lemma hdvd_nat_lit : f ∣ (X : (ZMod 29)[X]) ^ (Nat.card (ZMod 29)) ^ 10 - X := by
  rw [natCard_pow10]
  exact hdvd_lit

lemma h2_nat_lit : IsCoprime f ((X : (ZMod 29)[X]) ^ (Nat.card (ZMod 29)) ^ 2 - X) := by
  rw [natCard_pow2]
  exact h2_lit

lemma h5_nat_lit : IsCoprime f ((X : (ZMod 29)[X]) ^ (Nat.card (ZMod 29)) ^ 5 - X) := by
  rw [natCard_pow5]
  exact h5_lit

end S2122Mod29Split
