import tmp.sheaf.xif.paper.C3DonorUnconditionalActual
import tmp.sheaf.xif.paper.BasePlaceQCandidateActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology

/-! # Fmod-indexed BaseTensorData: actual carrier/insertion and exact missing unit

Task-664.  This file constructs the actual Fmod-indexed tensor index/places/
tuple and the actual one-factor insertion from the base completion into the
arithmetic tensor block, using the actual base place `nativeC3Place X`.

## Constructed

* `baseTensorIndex = PUnit`, `baseTensorPlaceIndex`, `baseTensorPlaces =
  nativeC3Place`, `baseTensorTuple = PUnit.unit`;
* `baseTensorBlock` = `ArithmeticTensorTupleBlock baseTensorPlaces
  baseTensorTuple`;
* `baseTensorInsertion : CommonPrimeCompletion (Fmod) nativeC3Place ->
  baseTensorBlock` via `finitePadicTensorTprod`;
* `baseTensorUnitOfNonzero` and `baseTensorLanding_q` (rfl) given the exact
  nonzero proof for the base q image.

## Exact missing

`BaseTensorUnitNonzero`: `baseTensorInsertion (baseQCandidateOfDescent X).q ≠ 0`.
No injectivity/nonzero theorem for the one-factor tensor insertion exists in
the tree.  Without it the base q image is not known to be a unit, so
`BaseTensorData.tensorUnit` cannot be constructed.  This is the exact missing
base tensor-unit/landing comparison; no arbitrary unit or fake landing is
chosen.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.BaseTensorDataCompleteAdapted

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C3DonorUnconditionalActual
open LeanFormal.IUT.N8Closure.C3DonorFieldsFromSource
open LeanFormal.IUT.XiFPaper.BasePlaceQCandidateActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor

universe ua uv upi umon ui

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Actual Fmod index: one factor. -/
abbrev baseTensorIndex : Type := PUnit

instance baseTensorIndexFintype : Fintype baseTensorIndex := inferInstance

/-- Actual Fmod place index: one factor. -/
abbrev baseTensorPlaceIndex : baseTensorIndex -> Type := fun _ => PUnit

/-- Actual Fmod tensor places: the native base place. -/
def baseTensorPlaces : (i : baseTensorIndex) -> baseTensorPlaceIndex i ->
    FinitePlaceAtPrime X.S.arithmetic.Fmod (nativeC3Prime X) :=
  fun _ _ => nativeC3Place X

/-- Actual Fmod tensor tuple: the unique point. -/
def baseTensorTuple : (i : baseTensorIndex) -> baseTensorPlaceIndex i :=
  fun _ => PUnit.unit

/-- The actual Fmod one-factor arithmetic tensor block. -/
abbrev baseTensorBlock : Type :=
  ArithmeticTensorTupleBlock baseTensorPlaces baseTensorTuple

/-- Actual insertion of the base completion into the one-factor tensor block. -/
noncomputable def baseTensorInsertion :
    CommonPrimeCompletion (K := X.S.arithmetic.Fmod) (nativeC3Place X) ->
      baseTensorBlock (X := X) :=
  fun z =>
    finitePadicTensorTprod (p := nativeC3Prime X)
      (M := fun _ : PUnit => CommonPrimeCompletion (nativeC3Place X))
      (fun _ => z)

theorem baseTensorInsertion_apply
    (z : CommonPrimeCompletion (K := X.S.arithmetic.Fmod) (nativeC3Place X)) :
    baseTensorInsertion X z =
      finitePadicTensorTprod (p := nativeC3Prime X)
        (M := fun _ : PUnit => CommonPrimeCompletion (nativeC3Place X))
        (fun _ => z) := rfl

/-- Exact missing nonzero proof for the base q image. -/
def BaseTensorUnitNonzero : Prop :=
  baseTensorInsertion X
      ((baseQCandidateOfDescent (X := X)).q :
        CommonPrimeCompletion (K := X.S.arithmetic.Fmod) (nativeC3Place X)) ≠ 0

/-- Conditional base tensor unit from the exact nonzero proof. -/
noncomputable def baseTensorUnitOfNonzero
    (hq : BaseTensorUnitNonzero (X := X)) :
    (baseTensorBlock (X := X))ˣ :=
  Units.mk0 (baseTensorInsertion X
    ((baseQCandidateOfDescent (X := X)).q :
      CommonPrimeCompletion (K := X.S.arithmetic.Fmod) (nativeC3Place X))) hq

theorem baseTensorUnitOfNonzero_coe
    (hq : BaseTensorUnitNonzero (X := X)) :
    (baseTensorUnitOfNonzero X hq : baseTensorBlock (X := X)) =
      baseTensorInsertion X
        ((baseQCandidateOfDescent (X := X)).q :
          CommonPrimeCompletion (K := X.S.arithmetic.Fmod) (nativeC3Place X)) :=
  rfl

/-- Conditional actual Fmod-indexed BaseTensorData from the exact nonzero
base q image proof. -/
noncomputable def baseTensorDataOfNonzero
    (hq : BaseTensorUnitNonzero (X := X)) :
    BaseTensorData (X := X) (baseQCandidateOfDescent (X := X)) where
  tensorIndex := baseTensorIndex
  tensorFintype := baseTensorIndexFintype
  tensorPlaceIndex := baseTensorPlaceIndex
  tensorPlaces := baseTensorPlaces X
  tensorTuple := baseTensorTuple X
  tensorUnit := baseTensorUnitOfNonzero X hq
  tensorLanding := baseTensorInsertion X
  tensorLanding_q := rfl

@[simp] theorem baseTensorDataOfNonzero_tensorUnit
    (hq : BaseTensorUnitNonzero (X := X)) :
    (baseTensorDataOfNonzero X hq).tensorUnit = baseTensorUnitOfNonzero X hq := rfl

@[simp] theorem baseTensorDataOfNonzero_tensorLanding
    (hq : BaseTensorUnitNonzero (X := X)) :
    (baseTensorDataOfNonzero X hq).tensorLanding = baseTensorInsertion X := rfl

theorem baseTensorDataOfNonzero_tensorLanding_q
    (hq : BaseTensorUnitNonzero (X := X)) :
    (baseTensorDataOfNonzero X hq).tensorLanding
        ((baseQCandidateOfDescent (X := X)).q :
          CommonPrimeCompletion (K := X.S.arithmetic.Fmod) (nativeC3Place X)) =
      ((baseTensorDataOfNonzero X hq).tensorUnit :
        baseTensorBlock (X := X)) :=
  rfl

end LeanFormal.IUT.XiFPaper.BaseTensorDataCompleteAdapted

end
