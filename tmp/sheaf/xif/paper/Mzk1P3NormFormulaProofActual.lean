/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange
import LeanFormal.IUT.Foundations.Geometry.FinitePlaceDegreeSumBound
import Mathlib.Tactic

/-! # P3 NORMFORMULA: residueNormBase = residueCharacteristic ^ residueInertiaDegree

GAP-labeled proof attempt; assembles the absolute-norm power formula from
Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver, under_eq_span_residueCharacteristic,
Ideal.inertiaDeg'_eq_inertiaDeg (new naming) and absNorm of a singleton span.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3NormFormulaProofActual

open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange

variable {K : Type*} [Field K] [NumberField K]

theorem residueNormBase_eq_residueCharacteristic_pow
    (place : NumberField.FinitePlace K) :
    residueNormBase place =
      (residueCharacteristic place : ℝ) ^ residueInertiaDegree place := by
  have hlies : place.maximalIdeal.asIdeal.LiesOver
      (Ideal.span {(residueCharacteristic place : ℤ)}) :=
    ⟨(under_eq_span_residueCharacteristic (K := K) place).symm⟩
  have hprime : (Ideal.span {(residueCharacteristic place : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by
      exact_mod_cast (residueCharacteristic_prime (K := K) place).ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp (residueCharacteristic_prime (K := K) place))
  have hne : (Ideal.span {(residueCharacteristic place : ℤ)}) ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast (residueCharacteristic_prime (K := K) place).ne_zero
  have hmax : (Ideal.span {(residueCharacteristic place : ℤ)}).IsMaximal :=
    IsPrime.to_maximal_ideal hne
  have hqmax : place.maximalIdeal.asIdeal.IsMaximal :=
    place.maximalIdeal.isPrime.isMaximal place.maximalIdeal.ne_bot
  haveI := hlies
  haveI := hmax
  haveI := hqmax
  have h := Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver
    place.maximalIdeal.asIdeal (Ideal.span {(residueCharacteristic place : ℤ)}) hprime hne
  have hidx : (Ideal.span {(residueCharacteristic place : ℤ)}).inertiaDeg'
      place.maximalIdeal.asIdeal = place.maximalIdeal.asIdeal.inertiaDeg ℤ :=
    Ideal.inertiaDeg'_eq_inertiaDeg (Ideal.span {(residueCharacteristic place : ℤ)})
      place.maximalIdeal.asIdeal
  have hnorm : Ideal.absNorm (Ideal.span {(residueCharacteristic place : ℤ)}) =
      residueCharacteristic place := by
    rw [Ideal.absNorm_span_singleton]
    simp
  have hnat : Ideal.absNorm place.maximalIdeal.asIdeal =
      residueCharacteristic place ^ place.maximalIdeal.asIdeal.inertiaDeg ℤ := by
    rw [h, hidx, hnorm]
  unfold residueNormBase residueInertiaDegree
  exact_mod_cast hnat

end LeanFormal.IUT.XiFPaper.Mzk1P3NormFormulaProofActual

end
