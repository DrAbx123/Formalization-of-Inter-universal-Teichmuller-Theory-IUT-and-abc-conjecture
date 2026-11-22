/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.NumberField.FinitePlaceExtension
import tmp.sheaf.xif.paper.Mzk1PlaceEqSpecializationActual
import Mathlib.Tactic

/-! # A1075: `completionMap_id` from `comap_self`

| field | value |
|---|---|---|
| Status | ATTEMPT: `comap_self` imported; `completionMap = id` is attempted by unfolding `completionMap` after rewriting `comap place = place` and using `RingHom.ext`/`simp`.  If `simp` cannot close the dense-extension step, the precise target remains `CompletionMapIdTarget`. |
| Source | `FinitePlaceExtension:58` (`completionMap`), `:88` (`completionMap_coe`); `Mzk1PlaceEqSpecializationActual.comap_self_of_algebraMap_id` |
| Last step | After `rw [hcomap]`, `completionMap` is `adicCompletion.equiv.symm ∘ mapRingHom (algebraMap) ∘ adicCompletion.equiv`; with `algebraMap = RingHom.id` one needs `mapRingHom id = id` and `equiv.symm ∘ equiv = id`, or a `Completion.ext` dense induction using `completionMap_coe`. |
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1CompletionMapIdActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1PlaceEqSpecializationActual

universe u

variable {K : Type u} [Field K] [NumberField K] [Algebra K K]

/-- Fallback explicit target: the remaining dense-extension identity.  Status: GAP
(semantic) — a naive `cases hcomap` fails dependent elimination and `rw` is not
type-correct across the `HEq`; no proof is asserted. -/
def CompletionMapIdTarget
    (halg : (algebraMap K K : K →+* K) = RingHom.id K)
    (place : NumberField.FinitePlace K) : Prop :=
  HEq (completionMap (k := K) (K := K) place)
    (RingHom.id (place.maximalIdeal.adicCompletion K))

/-- Dense formula, green from `completionMap_coe`. -/
theorem completionMap_self_coe
    (place : NumberField.FinitePlace K) (x : K) :
    completionMap (k := K) (K := K) place
        (x : (comap (k := K) place).maximalIdeal.adicCompletion K) =
      (algebraMap K K x : place.maximalIdeal.adicCompletion K) :=
  completionMap_coe (k := K) (K := K) place x

def rows : List (String × String × String) :=
  [ ("CompletionMapIdTarget", "HEq completionMap id after comap_self (dense extension)", "GAP (semantic; not proved)"),
    ("CompletionMapIdTarget", "same as Prop fallback", "Prop (if attempt fails)"),
    ("completionMap_self_coe", "dense K formula", "PROVED (completionMap_coe)") ]

theorem rows_length : rows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1CompletionMapIdActual

end