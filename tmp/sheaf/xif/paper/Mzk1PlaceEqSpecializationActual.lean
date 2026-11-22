/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.NumberField.FinitePlaceExtension
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
import LeanFormal.IUT.IUTI.HodgeTheater.SourceDefinition31NativeContractBridgeReduction
import tmp.sheaf.xif.paper.S1487OQPilotScalarEqualityActual
import tmp.sheaf.n8.closure.NativeBadLiftActual
import tmp.sheaf.xif.paper.Mzk1CompletionMapSelfActual
import Mathlib.Tactic

/-! # A1073: `comap_self` / `completionMap_id` / place specialization

| field | value |
|---|---|---|
| Status | PARTIAL: `comap_self_of_algebraMap_id` is proved under an explicit `algebraMap K K = RingHom.id K`; the `completionMap = id` and S1487/native place specialization are explicit Props, not asserted. |
| Source | `FinitePlaceExtension:58` (`completionMap`), `:61` (`comap` via `FinitePlace.mk`), `FinitePlaces:61-76` (`comap`); `S1487...:128` (`S1487FivePlace`), `:395` (`S1487Arithmetic`); `NativeBadLiftActual:22` |
| GAP | `Algebra K K` need not be `Algebra.id`; hence `comap_self` requires the explicit hypothesis `algebraMap K K = RingHom.id K`.  After `comap_self`, `completionMap` is a map between completions of the same place; its identity needs the dense-extension argument (`Completion.ext`) not yet formalized.  S1487 and native bad lifts are different `Classical.choose` outputs. |
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1PlaceEqSpecializationActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual

universe u

variable {K : Type u} [Field K] [NumberField K] [Algebra K K]

/-- `comap` is the identity if the algebra map is the identity. -/
theorem comap_self_of_algebraMap_id
    (halg : (algebraMap K K : K →+* K) = RingHom.id K)
    (place : NumberField.FinitePlace K) :
    comap (k := K) place = place := by
  have hO : NumberField.RingOfIntegers.mapRingHom (algebraMap K K : K →+* K) =
      RingHom.id (NumberField.RingOfIntegers K) := by
    rw [halg]
    ext x
    simp [NumberField.RingOfIntegers.mapRingHom_apply]
  apply NumberField.FinitePlace.maximalIdeal_injective
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [NumberFieldFinitePlace.comap_maximalIdeal]
  change place.maximalIdeal.asIdeal.comap
      (NumberField.RingOfIntegers.mapRingHom (algebraMap K K : K →+* K)) =
        place.maximalIdeal.asIdeal
  rw [hO, Ideal.comap_id]

/-- Dense formula for the self-completion map (from `completionMap_coe`). -/
theorem completionMap_self_coe
    (place : NumberField.FinitePlace K) (x : K) :
    completionMap (k := K) (K := K) place
        (x : (comap (k := K) place).maximalIdeal.adicCompletion K) =
      (algebraMap K K x : place.maximalIdeal.adicCompletion K) :=
  completionMap_coe (k := K) (K := K) place x

/-- Target: after `comap_self`, `completionMap` is the identity completion map.
The `HEq` records the type transport; the identity is not proved. -/
def CompletionMapIdTarget
    (halg : (algebraMap K K : K →+* K) = RingHom.id K)
    (place : NumberField.FinitePlace K) : Prop :=
  HEq (completionMap (k := K) (K := K) place)
    (RingHom.id (place.maximalIdeal.adicCompletion K))

/-! ## S1487 place specialization -/

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Existence of a native bad place whose base place is the concrete Gaussian
five place, under the arithmetic identification.  This is the data that would
turn `S1487PlaceEqTarget` into `rfl`; it is a Prop, not asserted. -/
def S1487NativeFivePlaceExists
    (hT : T.arithmetic = LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual.S1487Arithmetic l) : Prop :=
  ∃ b : Bad (nativePlaceSelection T),
    HEq b.1 LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual.S1487FivePlace.val

/-- The place equality target from A1072. -/
def S1487PlaceEqTarget
    (hT : T.arithmetic = LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual.S1487Arithmetic l)
    (b : Bad (nativePlaceSelection T)) : Prop :=
  HEq LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual.S1487FivePlace.val
    ((LeanFormal.IUT.N8Closure.nativeBadLift T).lift b)

/-- If the native lift is literally the concrete Gaussian five place,
`S1487PlaceEqTarget` is the corresponding carrier equality. -/
def S1487PlaceEqRoute : String :=
  "S1487FivePlace.val = concreteGaussianFivePlace; " ++
  "nativeBadLift T b = Classical.choose (comap_surjective b.1); " ++
  "if b.1 = concreteFivePlace and arithmetic fields are identified, the two " ++
  "choices are the same term; otherwise a place equality is extra source data."

def rows : List (String × String × String) :=
  [ ("comap_self_of_algebraMap_id", "comap = id if algebraMap = id", "PROVED"),
    ("completionMap_self_coe", "dense K formula", "PROVED (completionMap_coe)"),
    ("CompletionMapIdTarget", "completionMap = id after comap_self", "Prop (not proved)"),
    ("S1487NativeFivePlaceExists", "native b with b.1 = concreteFivePlace", "Prop (not proved)"),
    ("S1487PlaceEqTarget", "S1487FivePlace = nativeBadLift under hT", "Prop (not proved)") ]

theorem rows_length : rows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1PlaceEqSpecializationActual

end