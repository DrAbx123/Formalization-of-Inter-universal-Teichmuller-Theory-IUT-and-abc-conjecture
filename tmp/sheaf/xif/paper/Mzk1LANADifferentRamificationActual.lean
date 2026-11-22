/- Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import tmp.sheaf.xif.paper.Mzk1LANALocalTheoryReadoutActual
import Mathlib.Tactic

/-! A517: LANA LocalTheory different/ramification layer (ordDifferent,
differentExponent, ramIdxAt) on the actual C3 place, built on the local-theory
readout file. Tame different exponent e-1 and its relations are recorded as
actual definitions/theorems (no new axioms). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1LANADifferentRamificationActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1LANALocalTheoryReadoutActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The normalized order of the different at the C3 place (LANA ordDifferent):
the tame different exponent e - 1. -/
noncomputable def c3OrdDifferent : Real :=
  (c3RamificationIndex C3 : Real) - 1

theorem c3OrdDifferent_constructed :
    c3OrdDifferent C3 = (c3RamificationIndex C3 : Real) - 1 := rfl

theorem c3OrdDifferent_eq_differentExponent :
    c3OrdDifferent C3 = c3DifferentExponent C3 := rfl

theorem c3OrdDifferent_nonneg : 0 <= c3OrdDifferent C3 := by
  unfold c3OrdDifferent
  have h : (1 : Real) <= (c3RamificationIndex C3 : Real) :=
    Nat.one_le_cast.mpr (c3RamificationIndex_pos C3)
  linarith

/-- The different ideal exponent (LANA differentExponent): ordDifferent + 1. -/
noncomputable def c3DifferentExponentReal : Real :=
  c3OrdDifferent C3 + 1

theorem c3DifferentExponentReal_eq :
    c3DifferentExponentReal C3 = (c3RamificationIndex C3 : Real) := by
  unfold c3DifferentExponentReal c3OrdDifferent
  ring

/-- The ramification index at a place (LANA ramIdxAt), for the single-place
index type of the C3 source. -/
noncomputable def c3RamIdxAt (place : Fin 1) : Nat :=
  c3RamificationIndex C3

theorem c3RamIdxAt_const (place : Fin 1) :
    c3RamIdxAt C3 place = c3RamificationIndex C3 := rfl

/-- The tame different/ramification relation: different exponent = ramification - 1. -/
theorem c3_different_eq_ramification_sub_one :
    c3OrdDifferent C3 = (c3RamificationIndex C3 : Real) - 1 := rfl

/-- The different layer data object. -/
structure DifferentRamificationData
    (C3 : SourcePilotRegionData (l := l) (V := V) I) where
  ramificationIndex : Nat
  ramificationIndex_eq : ramificationIndex = c3RamificationIndex C3
  ordDifferent : Real
  ordDifferent_eq : ordDifferent = c3OrdDifferent C3
  differentExponent : Real
  differentExponent_eq : differentExponent = c3OrdDifferent C3 + 1

noncomputable def differentRamificationData :
    DifferentRamificationData C3 where
  ramificationIndex := c3RamificationIndex C3
  ramificationIndex_eq := rfl
  ordDifferent := c3OrdDifferent C3
  ordDifferent_eq := rfl
  differentExponent := c3OrdDifferent C3 + 1
  differentExponent_eq := rfl

theorem differentRamificationData_constructed :
    (differentRamificationData C3).ramificationIndex = c3RamificationIndex C3 ∧
    (differentRamificationData C3).differentExponent = c3OrdDifferent C3 + 1 := by
  refine ⟨rfl, rfl⟩

end LeanFormal.IUT.XiFPaper.Mzk1LANADifferentRamificationActual