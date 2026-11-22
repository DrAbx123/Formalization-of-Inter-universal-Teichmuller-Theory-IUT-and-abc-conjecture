import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing
import tmp.sheaf.xif.paper.JacobiFormalProductExpansions

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncCoeffJacobiConsumerAdapted

universe u

noncomputable def thetaTermEx (K : Type u) [Field K] (n : Int) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  HahnSeries.single (thetaQExponent n)
    (HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n))

noncomputable def thetaPairTerm (K : Type u) [Field K] (n : Int) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  thetaTermEx K n + thetaTermEx K (-n - 1)

theorem thetaPairTerm_coeff (K : Type u) [Field K] (n : Int) :
    (thetaPairTerm K n).coeff (thetaQExponent n) =
      HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n) +
        HahnSeries.single (thetaUExponent (-n - 1)) ((-1 : K) ^ (-n - 1)) := by
  unfold thetaPairTerm thetaTermEx
  rw [thetaQExponent_neg_succ]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single]

theorem thetaPairTerm_coeff_ne (K : Type u) [Field K] (n : Int) (e : HalfInt)
    (h : thetaQExponent n ≠ e) :
    (thetaPairTerm K n).coeff e = 0 := by
  unfold thetaPairTerm thetaTermEx
  rw [thetaQExponent_neg_succ]
  simp [thetaTermEx, HahnSeries.coeff_add, HahnSeries.coeff_single, h]

theorem thetaQExponent_injective_nonneg {a b : Int}
    (ha : 0 <= a) (hb : 0 <= b) (h : thetaQExponent a = thetaQExponent b) :
    a = b := by
  have hfac : ((a : Rat) - (b : Rat)) * ((a : Rat) + (b : Rat) + 1) = 0 := by
    unfold thetaQExponent at h
    nlinarith
  rcases mul_eq_zero.mp hfac with h1 | h2
  · exact_mod_cast (sub_eq_zero.mp h1)
  · exfalso
    have h2' : (a : Rat) + (b : Rat) + 1 = 0 := h2
    have ha' : (0 : Rat) <= a := by exact_mod_cast ha
    have hb' : (0 : Rat) <= b := by exact_mod_cast hb
    linarith

noncomputable def etaleThetaSymmetricTrunc (K : Type u) [Field K] (N : Nat) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  Finset.sum (Finset.range (N + 1)) (fun k : Nat =>
    thetaPairTerm K (k : Int))

theorem etaleThetaSymmetricTrunc_coeff_general (K : Type u) [Field K]
    (N n : Nat) (hN : n <= N) :
    (etaleThetaSymmetricTrunc K N).coeff (thetaQExponent (n : Int)) =
      HahnSeries.single (thetaUExponent (n : Int)) ((-1 : K) ^ (n : Int)) +
        HahnSeries.single (thetaUExponent (-(n : Int) - 1))
          ((-1 : K) ^ (-(n : Int) - 1)) := by
  rw [etaleThetaSymmetricTrunc, HahnSeries.coeff_sum]
  rw [Finset.sum_eq_single n]
  · exact thetaPairTerm_coeff K (n : Int)
  · intro k hk hkn
    have hk' : (k : Nat) <= N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hne : thetaQExponent (k : Int) ≠ thetaQExponent (n : Int) := by
      intro h
      have hEq : (k : Int) = (n : Int) := thetaQExponent_injective_nonneg
        (by positivity) (by positivity) h
      exact hkn (by omega)
    exact thetaPairTerm_coeff_ne K (k : Int) (thetaQExponent (n : Int)) hne
  · intro hn
    exact absurd (Finset.mem_range.mpr (by omega)) hn

open LeanFormal.IUT.XiFPaper.TateJacobiHahnAttempt

/-- Jacobi coefficient consumer: the finite Jacobi product coefficient is
    exactly the coefficient of the three q-binomial expansions. -/
theorem jacobiFormalProduct_coeff_threeExpansions (K : Type u) [Field K]
    (z : K) (N : Nat) (k : Int) :
    (jacobiFormalProduct z N).coeff k =
      ((Finset.sum (Finset.range (N + 1)) (fun j : Nat =>
          LeanFormal.IUT.XiFPaper.QBinomialCommRing.qBinoTermC
            (K := HahnSeries Int K) N j (formalR ^ 4)
            (HahnSeries.C z * formalR ^ 2))) *
        (Finset.sum (Finset.range (N + 1)) (fun j : Nat =>
          LeanFormal.IUT.XiFPaper.QBinomialCommRing.qBinoTermC
            (K := HahnSeries Int K) N j (formalR ^ 4)
            (HahnSeries.C z⁻¹ * formalR ^ 2))) *
          (Finset.sum (Finset.range (N + 1)) (fun j : Nat =>
            LeanFormal.IUT.XiFPaper.QBinomialCommRing.qBinoTermC
              (K := HahnSeries Int K) N j (formalR ^ 4)
              (-(formalR ^ 4))))).coeff k := by
  rw [LeanFormal.IUT.XiFPaper.JacobiFormalProductExpansions.jacobiFormalProduct_eq_threeExpansions]

#check etaleThetaSymmetricTrunc_coeff_general
#check jacobiFormalProduct_coeff_threeExpansions

end LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncCoeffJacobiConsumerAdapted
