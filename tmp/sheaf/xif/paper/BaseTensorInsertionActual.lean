import tmp.sheaf.xif.paper.C3DonorUnconditionalActual
import tmp.sheaf.xif.paper.BasePlaceQCandidateActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology
import Mathlib

/-! # One-factor tensor insertion nonzero and full BaseTensorData

Task-680. The actual one-factor insertion into the Fmod arithmetic tensor
block is shown nonzero/injective on nonzero factors by the realized tensor
coordinate basis. This constructs BaseTensorUnitNonzero and the full
BaseTensorData from an actual base q descent, without an arbitrary unit.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.BaseTensorInsertionActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.XiFPaper.C3DonorUnconditionalActual
open LeanFormal.IUT.XiFPaper.C3DonorFieldsFromSource
open LeanFormal.IUT.XiFPaper.BasePlaceQCandidateActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor

universe ua uv upi umon ui

variable {l : PrimeGeFive} (X : N8NativeInput l)

theorem finitePadicTensorTprod_single_ne_zero
    {p : Nat} [Fact p.Prime] {M : Type*}
    [NormedAddCommGroup M] [NormedSpace ℚ_[p] M] [FiniteDimensional ℚ_[p] M]
    (x : M) (hx : x ≠ 0) :
    finitePadicTensorTprod (p := p) (fun _ : Unit => M) (fun _ => x) ≠ 0 := by
  intro hzero
  have hcoord := congrArg
    (finitePadicTensorCoordinates (p := p) (fun _ : Unit => M)) hzero
  have hrepr : (Module.finBasis ℚ_[p] M).repr x = 0 := by
    ext k
    have hk := congrArg
      (fun F : FinitePadicTensorIndex (p := p) (fun _ : Unit => M) → ℚ_[p] =>
        F (fun _ : Unit => k)) hcoord
    simpa [finitePadicTensorCoordinates_tprod] using hk
  exact hx ((Module.finBasis ℚ_[p] M).repr.injective (by simpa using hrepr))

abbrev baseTensorIndex : Type := Unit
instance baseTensorIndexFintype : Fintype baseTensorIndex := inferInstance
abbrev baseTensorPlaceIndex : baseTensorIndex -> Type := fun _ => Unit

def baseTensorPlaces (X : N8NativeInput l) :
    (i : baseTensorIndex) -> baseTensorPlaceIndex i ->
      FinitePlaceAtPrime X.S.arithmetic.Fmod (nativeC3Prime X) :=
  fun _ _ => nativeC3Place X

def baseTensorTuple (X : N8NativeInput l) :
    (i : baseTensorIndex) -> baseTensorPlaceIndex i :=
  fun _ => ()

abbrev baseTensorBlock (X : N8NativeInput l) : Type :=
  ArithmeticTensorTupleBlock (baseTensorPlaces X) (baseTensorTuple X)

noncomputable def baseTensorInsertion :
    CommonPrimeCompletion (K := X.S.arithmetic.Fmod) (nativeC3Place X) ->
      baseTensorBlock X :=
  fun z => finitePadicTensorTprod (p := nativeC3Prime X)
    (M := fun _ : Unit => CommonPrimeCompletion (nativeC3Place X))
    (fun _ => z)

theorem baseTensorInsertion_ne_zero
    (q : FinitePlaceQCandidate (nativeC3Place X).val) (hq : q.q ≠ 0) :
    baseTensorInsertion X q.q ≠ 0 := by
  unfold baseTensorInsertion
  exact finitePadicTensorTprod_single_ne_zero (p := nativeC3Prime X)
    (M := CommonPrimeCompletion (nativeC3Place X)) q.q hq

theorem baseTensorUnitNonzero_of_descent (D : BaseQDescentData (X := X)) :
    baseTensorInsertion X (baseQCandidateOfDescent (X := X) D).q ≠ 0 :=
  baseTensorInsertion_ne_zero X (baseQCandidateOfDescent (X := X) D)
    (baseQCandidateOfDescent (X := X) D).q_ne_zero

noncomputable def baseTensorDataActual (D : BaseQDescentData (X := X)) :
    BaseTensorData (X := X) (baseQCandidateOfDescent (X := X) D) where
  tensorIndex := baseTensorIndex
  tensorFintype := baseTensorIndexFintype
  tensorPlaceIndex := baseTensorPlaceIndex
  tensorPlaces := baseTensorPlaces X
  tensorTuple := baseTensorTuple X
  tensorUnit := Units.mk0
    (baseTensorInsertion X (baseQCandidateOfDescent (X := X) D).q)
    (baseTensorUnitNonzero_of_descent X D)
  tensorLanding := baseTensorInsertion X
  tensorLanding_q := rfl

@[simp] theorem baseTensorDataActual_tensorLanding
    (D : BaseQDescentData (X := X)) :
    (baseTensorDataActual X D).tensorLanding = baseTensorInsertion X := rfl

theorem baseTensorDataActual_tensorLanding_q
    (D : BaseQDescentData (X := X)) :
    (baseTensorDataActual X D).tensorLanding
        (baseQCandidateOfDescent (X := X) D).q =
      ((baseTensorDataActual X D).tensorUnit : baseTensorBlock X) :=
  rfl

theorem baseTensorDataActual_tensorUnit_ne_zero
    (D : BaseQDescentData (X := X)) :
    ((baseTensorDataActual X D).tensorUnit : baseTensorBlock (X := X)) ≠ 0 :=
  Units.ne_zero (baseTensorDataActual X D).tensorUnit

theorem baseTensorDataActual_nonempty
    (D : BaseQDescentData (X := X)) :
    Nonempty (BaseTensorData (X := X) (baseQCandidateOfDescent (X := X) D)) :=
  ⟨baseTensorDataActual X D⟩

end LeanFormal.IUT.XiFPaper.BaseTensorInsertionActual

end
