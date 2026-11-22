/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.NumberField.FinitePlaceExtension
import tmp.sheaf.xif.paper.S1487OQPilotScalarEqualityActual
import tmp.sheaf.n8.closure.NativeBadLiftActual
import Mathlib.Tactic

/-! # A1072: `completionMap` self-target and S1487/native place equality

| field | value |
|---|---|---|
| Status | PARTIAL: the dense-field formula `completionMap_coe` is proved; the full identity `completionMap = RingHom.id` and the S1487/native place equality are recorded as explicit **Props**, not asserted. |
| Source | `FinitePlaceExtension:58` (`completionMap`), `:88` (`completionMap_coe`), `:72` (`continuous_completionMap`); `S1487FivePlace` (`S1487...:128`); `nativeBadLift` (`NativeBadLiftActual:22`), `nativeBadLift_comap` (`NativeReductionFieldsActual:91`) |
| GAP | `completionMap` has domain `(comap place).adicCompletion K` and codomain `place.adicCompletion K`; even with `Algebra K K`, `comap place = place` and the identity on completions need a dense-extension argument.  `S1487FivePlace` and `nativeBadLift T b` are two `Classical.choose` outputs from different `comap_surjective` propositions; no equality theorem. |
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1CompletionMapSelfActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual

universe u

variable {K : Type u} [Field K] [NumberField K] [Algebra K K]

/-- On the dense base field, the self-`completionMap` is the algebra map.  This
is a direct instance of `completionMap_coe` (no identity claim yet). -/
theorem completionMap_self_coe (place : NumberField.FinitePlace K) (x : K) :
    completionMap (k := K) (K := K) place
        (x : (comap (k := K) place).maximalIdeal.adicCompletion K) =
      (algebraMap K K x : place.maximalIdeal.adicCompletion K) :=
  completionMap_coe (k := K) (K := K) place x

/-- **Self-map target**: after identifying `comap place` with `place`, the
completion map is heterogeneously equal to the identity.  The equality of
places is an explicit witness; the map identity is not proved here. -/
def CompletionMapSelfTarget (place : NumberField.FinitePlace K) : Prop :=
  ∃ _h : comap (k := K) place = place,
    HEq (completionMap (k := K) (K := K) place)
      (RingHom.id (place.maximalIdeal.adicCompletion K))

/-- Exact identity target with the `comap` equality fixed. -/
def CompletionMapSelfTargetOfComap (place : NumberField.FinitePlace K)
    (h : comap (k := K) place = place) : Prop :=
  HEq (completionMap (k := K) (K := K) place)
    (RingHom.id (place.maximalIdeal.adicCompletion K))

/-! ## S1487 / native place equality -/

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The S1487 Gaussian five place and the native bad lift live in the same
field after the arithmetic equality `T.arithmetic = S1487Arithmetic l`.  The
place equality is an explicit Prop target. -/
def S1487PlaceEqTarget
    (hT : T.arithmetic = LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual.S1487Arithmetic l)
    (b : Bad (nativePlaceSelection T)) : Prop :=
  HEq LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual.S1487FivePlace.val
    ((LeanFormal.IUT.N8Closure.nativeBadLift T).lift b)

/-- If the two `Classical.choose` outputs come from the same `comap_surjective`
proposition, `Classical.choose_spec`/proof irrelevance can identify them; this
is the intended route, not a proved equality. -/
def S1487PlaceEqRoute : String :=
  "S1487FivePlace = Classical.choose (comap_surjective ... concreteFivePlace); " ++
  "nativeBadLift T b = Classical.choose (comap_surjective ... b.1); " ++
  "if b.1 is the same rational place and the arithmetic fields are identified, " ++
  "the two choices are the same term; otherwise a place equality is extra data."

def rows : List (String × String × String) :=
  [ ("completionMap_self_coe", "dense K formula", "PROVED (completionMap_coe)"),
    ("CompletionMapSelfTarget", "HEq completionMap id + comap equality", "Prop (not proved)"),
    ("S1487PlaceEqTarget", "S1487FivePlace = nativeBadLift under hT", "Prop (not proved)"),
    ("S1487PlaceEqRoute", "Classical.choose comparison route", "NOTE") ]

theorem rows_length : rows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1CompletionMapSelfActual

end