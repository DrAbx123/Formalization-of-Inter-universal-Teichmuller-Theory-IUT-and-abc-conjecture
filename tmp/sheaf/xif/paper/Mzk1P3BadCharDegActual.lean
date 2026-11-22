/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P3NormFormulaProofActual
import Mathlib.Tactic

/-! # P3 BADCHAR-DEG: residue inertia degree one iff absNorm equals residue characteristic

Green equivalence from NORMFORMULA (green) plus log-injectivity of the positive prime.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3BadCharDegActual

open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.Mzk1P3NormFormulaProofActual

variable {K : Type*} [Field K] [NumberField K]

theorem residueInertiaDegree_eq_one_iff_absNorm_eq
    (place : NumberField.FinitePlace K) :
    residueInertiaDegree place = 1 ↔
      (Ideal.absNorm place.maximalIdeal.asIdeal : ℝ) = residueCharacteristic place := by
  have hpow := residueNormBase_eq_residueCharacteristic_pow (K := K) place
  have hrepr : residueNormBase place =
      (Ideal.absNorm place.maximalIdeal.asIdeal : ℝ) := rfl
  constructor
  · intro h
    rw [hrepr] at hpow
    rw [h, pow_one] at hpow
    exact hpow
  · intro h
    have hpow1 : (residueCharacteristic place : ℝ) ^ residueInertiaDegree place =
        residueCharacteristic place := by
      rw [← hpow, hrepr, h]
    have hbase : (1 : ℝ) < residueCharacteristic place := by
      exact_mod_cast (residueCharacteristic_prime (K := K) place).one_lt
    have hlog := congrArg Real.log hpow1
    rw [Real.log_pow] at hlog
    have hlogpos : 0 < Real.log (residueCharacteristic place : ℝ) := Real.log_pos hbase
    have h1 : (residueInertiaDegree place : ℝ) *
        Real.log (residueCharacteristic place : ℝ) =
        1 * Real.log (residueCharacteristic place : ℝ) := by
      simpa using hlog
    have hcast : (residueInertiaDegree place : ℝ) = 1 :=
      mul_right_cancel₀ (ne_of_gt hlogpos) h1
    exact_mod_cast hcast

def badCharDegRows : List (String × String × String) :=
  [ ("residueInertiaDegree_eq_one_iff_absNorm_eq", "f = 1 iff absNorm = residue characteristic", "PROVED (from NORMFORMULA)") ]

theorem badCharDegRows_length : badCharDegRows.length = 1 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P3BadCharDegActual

end
