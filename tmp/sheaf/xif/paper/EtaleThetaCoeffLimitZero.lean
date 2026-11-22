import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoeffLimitZero

universe u

abbrev HalfInt : Type := Rat

def thetaQExponent (n : Int) : HalfInt := (n : Rat) * ((n : Rat) + 1) / 2

def thetaUExponent (n : Int) : Int := 2 * n + 1

noncomputable def thetaTermEx (K : Type u) [Field K] (n : Int) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  HahnSeries.single (thetaQExponent n)
    (HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n))

noncomputable def etaleThetaTruncOneSided (K : Type u) [Field K] (N : Nat) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  Finset.sum (Finset.range (N + 1)) (fun k : Nat =>
    thetaTermEx K (k : Int))

theorem etaleThetaTruncOneSided_succ (K : Type u) [Field K] (N : Nat) :
    etaleThetaTruncOneSided K (N + 1) =
      etaleThetaTruncOneSided K N + thetaTermEx K (N + 1 : Int) := by
  simp [etaleThetaTruncOneSided, Finset.sum_range_succ]

theorem thetaQExponent_succ_ne_zero (N : Nat) :
    thetaQExponent (N + 1 : Int) ≠ 0 := by
  unfold thetaQExponent
  have h : (0 : Rat) < ((N : Rat) + 1) := by positivity
  have h' : (0 : Rat) < ((N : Rat) + 2) := by positivity
  positivity

theorem etaleThetaTruncOneSided_coeff_zero_all (K : Type u) [Field K]
    (N : Nat) :
    (etaleThetaTruncOneSided K N).coeff (0 : HalfInt) =
      HahnSeries.single (thetaUExponent 0) (1 : K) := by
  induction N with
  | zero => simp [etaleThetaTruncOneSided, thetaQExponent, thetaUExponent]
  | succ N ih =>
      rw [etaleThetaTruncOneSided_succ, HahnSeries.coeff_add, ih]
      have hz : (thetaTermEx K (N + 1 : Int)).coeff (0 : HalfInt) = 0 := by
        simp [thetaTermEx, HahnSeries.coeff_single, thetaQExponent_succ_ne_zero N]
      rw [hz, add_zero]

theorem thetaQExponent_nat_ge (N : Nat) :
    ((N : Rat) + 1) <= thetaQExponent (N + 1 : Int) := by
  unfold thetaQExponent
  have hN : (0 : Rat) <= (N : Rat) := by positivity
  nlinarith

theorem thetaQExponent_unbounded (e : HalfInt) :
    exists N : Nat, e < thetaQExponent (N + 1 : Int) := by
  obtain ⟨N, hN⟩ := exists_nat_gt e
  refine ⟨N, ?_⟩
  have hle := thetaQExponent_nat_ge N
  have hN' : e < (N : Rat) := hN
  linarith

theorem thetaQExponent_nat_mono {a b : Nat} (h : a <= b) :
    thetaQExponent (a + 1 : Int) <= thetaQExponent (b + 1 : Int) := by
  unfold thetaQExponent
  have hab : (a : Rat) <= (b : Rat) := by exact_mod_cast h
  nlinarith

theorem etaleThetaTruncOneSided_coeff_stable_of_lt (K : Type u) [Field K]
    (N : Nat) (e : HalfInt) (h : e < thetaQExponent (N + 1 : Int)) :
    (etaleThetaTruncOneSided K (N + 1)).coeff e =
      (etaleThetaTruncOneSided K N).coeff e := by
  rw [etaleThetaTruncOneSided_succ, HahnSeries.coeff_add]
  have hne : e ≠ thetaQExponent (N + 1 : Int) := ne_of_lt h
  have hz : (thetaTermEx K (N + 1 : Int)).coeff e = 0 := by
    simp [thetaTermEx, HahnSeries.coeff_single, hne]
  rw [hz, add_zero]

theorem etaleThetaTruncOneSided_coeff_eventually_stable (K : Type u) [Field K]
    (e : HalfInt) :
    exists N0 : Nat, forall N : Nat, N0 <= N ->
      (etaleThetaTruncOneSided K (N + 1)).coeff e =
        (etaleThetaTruncOneSided K N).coeff e := by
  obtain ⟨N0, hN0⟩ := thetaQExponent_unbounded e
  refine ⟨N0, ?_⟩
  intro N hN
  have hmono := thetaQExponent_nat_mono hN
  have hlt : e < thetaQExponent (N + 1 : Int) := lt_of_lt_of_le hN0 hmono
  exact etaleThetaTruncOneSided_coeff_stable_of_lt K N e hlt

noncomputable def etaleThetaCoeffLimit (K : Type u) [Field K] (e : HalfInt) :
    HahnSeries Int K :=
  (etaleThetaTruncOneSided K
    (Classical.choose (etaleThetaTruncOneSided_coeff_eventually_stable K e))).coeff e

theorem etaleThetaCoeffLimit_zero (K : Type u) [Field K] :
    etaleThetaCoeffLimit K (0 : HalfInt) =
      HahnSeries.single (thetaUExponent 0) (1 : K) := by
  unfold etaleThetaCoeffLimit
  exact etaleThetaTruncOneSided_coeff_zero_all K _

#check etaleThetaCoeffLimit_zero

end LeanFormal.IUT.XiFPaper.EtaleThetaCoeffLimitZero
