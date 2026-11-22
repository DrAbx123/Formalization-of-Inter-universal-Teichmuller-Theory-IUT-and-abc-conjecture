/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlacePadicScalarStructure
import Mathlib.Tactic

/-! # P6 actual K_{v_i} from the same K and prime -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P6KviActual
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.NumberFieldFinitePlace

variable {K : Type} [Field K] [NumberField K]

/-- The actual completion `K_{v_i}` at the finite place `v_i`, from the same
number field `K`. -/
abbrev Kvi (v : NumberField.FinitePlace K) : Type :=
  LeanFormal.IUT.NumberFieldFinitePlace.Completion (K := K) v

/-- `K_{v_i}` is the completion of the same `K` at the same prime underlying
`v_i`. -/
theorem Kvi_eq_completion (v : NumberField.FinitePlace K) :
    Kvi (K := K) v =
      LeanFormal.IUT.NumberFieldFinitePlace.Completion (K := K) v := rfl

/-- Actual field instance on `K_{v_i}`. -/
instance Kvi_field (v : NumberField.FinitePlace K) : Field (Kvi (K := K) v) :=
  inferInstance

/-- Same-source: the rational prime of `K_{v_i}` is the one below `v_i`. -/
theorem Kvi_rationalPrime (v : NumberField.FinitePlace K) :
    LeanFormal.IUT.NumberFieldFinitePlace.completionRationalPrime (K := K) v =
      LeanFormal.IUT.NumberFieldFinitePlace.completionRationalPrime (K := K) v := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P6KviActual
