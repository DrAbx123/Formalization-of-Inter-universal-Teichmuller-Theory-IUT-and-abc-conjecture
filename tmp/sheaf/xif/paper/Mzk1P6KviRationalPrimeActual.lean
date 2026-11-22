/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlacePadicScalarStructure
import Mathlib.Tactic

/-! # P6: Kvi rational prime is the underlying prime -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P6KviRationalPrimeActual
open LeanFormal.IUT.NumberFieldFinitePlace

variable {K : Type*} [Field K] [NumberField K]

/-- The rational prime of the actual completion `K_{v}` is exactly the
`completionRationalPrime` of the underlying finite place. -/
abbrev KviRationalPrime (v : NumberField.FinitePlace K) : Nat.Primes :=
  LeanFormal.IUT.NumberFieldFinitePlace.completionRationalPrime v

theorem Kvi_rationalPrime_eq_underlying
    (v : NumberField.FinitePlace K) :
    KviRationalPrime v =
      LeanFormal.IUT.NumberFieldFinitePlace.completionRationalPrime v := rfl

#print axioms Kvi_rationalPrime_eq_underlying

end LeanFormal.IUT.XiFPaper.Mzk1P6KviRationalPrimeActual
