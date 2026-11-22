/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.Geometry.FinitePlaceDegreeSumBound
import Mathlib.Tactic

/-! # P3 BADCHAR-PRIME: residue characteristic to under-ideal span (one direction)

CONDITIONAL file; the forward direction is green, the converse is a named input.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3BadCharPrimeActual

open LeanFormal.IUT.NumberFieldFinitePlace

variable {K : Type*} [Field K] [NumberField K]

theorem under_eq_span_of_residueCharacteristic_eq
    (place : NumberField.FinitePlace K) (q : ℕ)
    (h : residueCharacteristic place = q) :
    place.maximalIdeal.asIdeal.under ℤ = Ideal.span {(q : ℤ)} := by
  rw [under_eq_span_residueCharacteristic (K := K) place, h]

def BadCharPrimeUnderData (place : NumberField.FinitePlace K) (p : ℕ) : Prop :=
  place.maximalIdeal.asIdeal.under ℤ = Ideal.span {(p : ℤ)}

theorem badCharPrimeUnderData_of_residueCharacteristic_eq
    (place : NumberField.FinitePlace K) (p : ℕ)
    (h : residueCharacteristic place = p) :
    BadCharPrimeUnderData place p :=
  under_eq_span_of_residueCharacteristic_eq place p h

end LeanFormal.IUT.XiFPaper.Mzk1P3BadCharPrimeActual

end
