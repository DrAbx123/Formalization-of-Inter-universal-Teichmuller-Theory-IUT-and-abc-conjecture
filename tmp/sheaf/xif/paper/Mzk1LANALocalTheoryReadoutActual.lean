/- Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import tmp.sheaf.xif.paper.S3137C3LogShellPacketNormalizedLogVolumeActual
import LeanFormal.IUT.Foundations.NumberField.FinitePlaceExtension
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
import Mathlib.Tactic

/-! Reference/object file mirroring LANA latest Iut/Concrete/LocalTheory.lean
(localRamificationIndex/inertiaDegree/localDegree/placeWeight/ordp/differentExponent)
on the actual C3 place, with the old Mathlib primed ramification API. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1LANALocalTheoryReadoutActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.LocalFieldIntegralUnits

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The actual ramification index of the C3 place over Q. -/
noncomputable def c3RamificationIndex : Nat :=
  (comap (k := ℚ) C3.place.val).maximalIdeal.asIdeal.ramificationIdx'
    C3.place.val.maximalIdeal.asIdeal

theorem c3RamificationIndex_constructed :
    c3RamificationIndex C3 =
      (comap (k := ℚ) C3.place.val).maximalIdeal.asIdeal.ramificationIdx'
        C3.place.val.maximalIdeal.asIdeal := rfl

theorem c3RamificationIndex_pos : 0 < c3RamificationIndex C3 :=
  Nat.pos_of_ne_zero (ramificationIdx_ne_zero (k := ℚ) C3.place.val)

/-- The actual inertia degree of the C3 place over Q. -/
noncomputable def c3InertiaDegree : Nat :=
  (comap (k := ℚ) C3.place.val).maximalIdeal.asIdeal.inertiaDeg'
    C3.place.val.maximalIdeal.asIdeal

theorem c3InertiaDegree_constructed :
    c3InertiaDegree C3 =
      (comap (k := ℚ) C3.place.val).maximalIdeal.asIdeal.inertiaDeg'
        C3.place.val.maximalIdeal.asIdeal := rfl

/-- The local degree e * f (LANA localDeg). -/
noncomputable def c3LocalDegree : Nat :=
  c3RamificationIndex C3 * c3InertiaDegree C3

theorem c3LocalDegree_eq :
    c3LocalDegree C3 = c3RamificationIndex C3 * c3InertiaDegree C3 := rfl

/-- The place weight used by the normalized log-volume: local degree * log p. -/
noncomputable def c3PlaceWeight : Real :=
  (c3LocalDegree C3 : Real) * Real.log (C3.p : Real)

theorem c3PlaceWeight_constructed :
    c3PlaceWeight C3 = (c3LocalDegree C3 : Real) * Real.log (C3.p : Real) := rfl

/-- The normalized p-adic order (LANA ordp) of a completion element. -/
noncomputable def c3OrdP (x : CommonPrimeCompletion C3.place) : Real :=
  -Real.log ‖x‖ / Real.log (C3.p : Real)

theorem c3OrdP_constructed (x : CommonPrimeCompletion C3.place) :
    c3OrdP C3 x = -Real.log ‖x‖ / Real.log (C3.p : Real) := rfl

theorem c3OrdP_one : c3OrdP C3 (1 : CommonPrimeCompletion C3.place) = 0 := by
  unfold c3OrdP
  simp

/-- The tame different exponent e - 1 (LANA differentExponent, tame part). -/
noncomputable def c3DifferentExponent : Real :=
  (c3RamificationIndex C3 : Real) - 1

theorem c3DifferentExponent_eq :
    c3DifferentExponent C3 = (c3RamificationIndex C3 : Real) - 1 := rfl

/-- LANA LocalTheory-style readout data for the actual C3 place. -/
structure LANALocalTheoryReadout
    (C3 : SourcePilotRegionData (l := l) (V := V) I) where
  e : Nat
  e_eq : e = c3RamificationIndex C3
  f : Nat
  f_eq : f = c3InertiaDegree C3
  localDeg : Nat
  localDeg_eq : localDeg = c3LocalDegree C3
  placeWeight : Real
  placeWeight_eq : placeWeight = c3PlaceWeight C3
  differentExponent : Real
  differentExponent_eq : differentExponent = c3DifferentExponent C3

noncomputable def lanaLocalTheoryReadout :
    LANALocalTheoryReadout C3 where
  e := c3RamificationIndex C3
  e_eq := rfl
  f := c3InertiaDegree C3
  f_eq := rfl
  localDeg := c3LocalDegree C3
  localDeg_eq := rfl
  placeWeight := c3PlaceWeight C3
  placeWeight_eq := rfl
  differentExponent := c3DifferentExponent C3
  differentExponent_eq := rfl

theorem lanaLocalTheoryReadout_constructed :
    (lanaLocalTheoryReadout C3).e = c3RamificationIndex C3 ∧
    (lanaLocalTheoryReadout C3).f = c3InertiaDegree C3 ∧
    (lanaLocalTheoryReadout C3).localDeg = c3LocalDegree C3 := by
  refine ⟨rfl, rfl, rfl⟩

end LeanFormal.IUT.XiFPaper.Mzk1LANALocalTheoryReadoutActual