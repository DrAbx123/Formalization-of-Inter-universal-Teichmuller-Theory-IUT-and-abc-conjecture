/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.Geometry.FinitePlaceDegreeSumBound
import tmp.sheaf.xif.paper.Mzk1PrimeConductorRouteActual
import Mathlib.Tactic

/-! # P3 BADCHAR-PRIME equivalence: under-ideal span <-> residue characteristic

Green equivalence using under_eq_span_residueCharacteristic and absNorm of singleton
spans (natAbs equality).  This reduces BADCHAR-PRIME to the actual under-ideal
identification at the bad place.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3BadCharPrimeEquivActual

open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual

variable {K : Type*} [Field K] [NumberField K]

theorem under_eq_span_iff_residueCharacteristic_eq
    (place : NumberField.FinitePlace K) (C : PrimeConductorCurve) :
    place.maximalIdeal.asIdeal.under ℤ = Ideal.span {(C.p : ℤ)}
      ↔ residueCharacteristic place = C.p := by
  constructor
  · intro h
    have h1 : place.maximalIdeal.asIdeal.under ℤ =
        Ideal.span {(residueCharacteristic place : ℤ)} :=
      under_eq_span_residueCharacteristic (K := K) place
    have hspan : Ideal.span {(residueCharacteristic place : ℤ)} =
        Ideal.span {(C.p : ℤ)} := by rw [← h1, h]
    have hnorm := congrArg (fun I : Ideal ℤ => Ideal.absNorm I) hspan
    rw [Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton] at hnorm
    have hnat : residueCharacteristic place = C.p := by
      simpa using hnorm
    exact hnat
  · intro h
    rw [under_eq_span_residueCharacteristic (K := K) place, h]

def badCharPrimeEquivRows : List (String × String × String) :=
  [ ("under_eq_span_iff_residueCharacteristic_eq", "under ideal span C.p iff residue char = C.p", "PROVED") ]

theorem badCharPrimeEquivRows_length : badCharPrimeEquivRows.length = 1 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P3BadCharPrimeEquivActual

end
