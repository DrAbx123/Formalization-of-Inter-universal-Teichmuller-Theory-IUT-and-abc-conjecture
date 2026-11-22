/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion
import Mathlib.Tactic
/-! # Bundled ramified local place for Paper 3.12 per-place data -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1RamifiedPlaceActual
open LeanFormal.IUT.NumberFieldFinitePlace
/-- One actual ramified completion, bundled with its local-field instances. -/
structure RamifiedPlace where
  p : Nat
  [factPrime : Fact (Nat.Prime p)]
  K : Type*
  [normed : NormedField K]
  [charZero : CharZero K]
  [complete : CompleteSpace K]
  [ultrametric : IsUltrametricDist K]
  [proper : ProperSpace K]
  [alg : NormedAlgebra (Padic p) K]
  [finDim : FiniteDimensional (Padic p) K]
/-- The actual normalized completion of a number-field finite place. -/
def ofPlace {F : Type*} [Field F] [NumberField F]
    (place : NumberField.FinitePlace F) : RamifiedPlace where
  p := (completionRationalPrime place).val
  factPrime := inferInstance
  K := NormalizedCompletion place
  normed := inferInstance
  charZero := inferInstance
  complete := inferInstance
  ultrametric := inferInstance
  proper := inferInstance
  alg := inferInstance
  finDim := inferInstance
end LeanFormal.IUT.XiFPaper.Mzk1RamifiedPlaceActual
end