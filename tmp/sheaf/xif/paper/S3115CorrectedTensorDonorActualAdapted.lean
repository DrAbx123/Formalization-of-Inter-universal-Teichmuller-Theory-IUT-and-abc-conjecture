import tmp.sheaf.xif.paper.C3DonorFieldsFromSource
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.XiFPaper.C3DonorFieldsFromSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1600000

namespace LeanFormal.IUT.XiFPaper.S3115CorrectedTensorDonorActualAdapted

variable {l : PrimeGeFive} (X : N8NativeInput l)

structure NativeTensorLandingDonorActual where
  p : Nat
  [hp : Fact p.Prime]
  tensorIndex : Type
  [tensorFintype : Fintype tensorIndex]
  tensorPlaceIndex : tensorIndex -> Type
  tensorPlaces : (i : tensorIndex) -> tensorPlaceIndex i ->
    FinitePlaceAtPrime X.S.arithmetic.Fmod p
  tensorTuple : (i : tensorIndex) -> tensorPlaceIndex i
  q : FinitePlaceQCandidate (nativeC3Place X).val
  tensorUnit : (ArithmeticTensorTupleBlock tensorPlaces tensorTuple)ˣ
  tensorLanding : CommonPrimeCompletion (nativeC3Place X) ->
      ArithmeticTensorTupleBlock tensorPlaces tensorTuple
  tensorLanding_q : tensorLanding (q.q : CommonPrimeCompletion (nativeC3Place X)) =
      (tensorUnit : ArithmeticTensorTupleBlock tensorPlaces tensorTuple)

theorem S3115_tensorInsertion_ne_zero
    {p : Nat} [Fact p.Prime] {M : Type*}
    [NormedAddCommGroup M] [NormedSpace ℚ_[p] M] [FiniteDimensional ℚ_[p] M]
    (x : M) (hx : x ≠ 0) :
    finitePadicTensorTprod (p := p) (fun _ : Unit => M) (fun _ => x) ≠ 0 := by
  intro hzero
  have hcoord := congrArg (finitePadicTensorCoordinates (p := p) (fun _ : Unit => M)) hzero
  have hrepr : (Module.finBasis ℚ_[p] M).repr x = 0 := by
    ext k
    have hk := congrArg (fun F : FinitePadicTensorIndex (p := p) (fun _ : Unit => M) -> ℚ_[p] =>
        F (fun _ : Unit => k)) hcoord
    simpa [finitePadicTensorCoordinates_tprod] using hk
  exact hx ((Module.finBasis ℚ_[p] M).repr.injective (by simpa using hrepr))

abbrev S3115TensorBlock (X : N8NativeInput l) : Type :=
  ArithmeticTensorTupleBlock (fun _ : Unit => fun _ : Unit => nativeC3Place X) (fun _ => ())

noncomputable def S3115TensorInsertion : CommonPrimeCompletion (nativeC3Place X) -> S3115TensorBlock X :=
  fun z => finitePadicTensorTprod (p := nativeC3Prime X)
    (M := fun _ : Unit => CommonPrimeCompletion (nativeC3Place X)) (fun _ => z)

theorem S3115TensorInsertion_ne_zero (q : FinitePlaceQCandidate (nativeC3Place X).val) (hq : q.q ≠ 0) :
    S3115TensorInsertion X q.q ≠ 0 := S3115_tensorInsertion_ne_zero (p := nativeC3Prime X) q.q hq

noncomputable def S3115BaseQ : FinitePlaceQCandidate (nativeC3Place X).val :=
  Classical.choice (finitePlaceQCandidate_nonempty (nativeC3Place X).val)

noncomputable def S3115Donor : NativeTensorLandingDonorActual X where
  p := nativeC3Prime X
  hp := inferInstance
  tensorIndex := Unit
  tensorFintype := inferInstance
  tensorPlaceIndex := fun _ => Unit
  tensorPlaces := fun _ _ => nativeC3Place X
  tensorTuple := fun _ => ()
  q := S3115BaseQ X
  tensorUnit := Units.mk0 (S3115TensorInsertion X (S3115BaseQ X).q)
    (S3115TensorInsertion_ne_zero X (S3115BaseQ X) (S3115BaseQ X).q_ne_zero)
  tensorLanding := S3115TensorInsertion X
  tensorLanding_q := rfl

theorem S3115Donor_p : (S3115Donor X).p = nativeC3Prime X := rfl

theorem S3115Donor_tensorUnit_eq :
    ((S3115Donor X).tensorUnit : ArithmeticTensorTupleBlock (S3115Donor X).tensorPlaces (S3115Donor X).tensorTuple) =
    S3115TensorInsertion X (S3115BaseQ X).q := rfl

theorem S3115Donor_tensorUnit_ne_zero :
    ((S3115Donor X).tensorUnit : ArithmeticTensorTupleBlock (S3115Donor X).tensorPlaces (S3115Donor X).tensorTuple) ≠ 0 :=
  Units.ne_zero (S3115Donor X).tensorUnit

noncomputable def S3115DonorP5 (h5 : nativeC3Prime X = 5) : NativeTensorLandingDonorActual X :=
  let D := S3115Donor X
  { D with p := 5, hp := inferInstance }

#check NativeTensorLandingDonorActual
#check S3115BaseQ
#check S3115Donor
#check S3115Donor_tensorUnit_ne_zero
#check S3115DonorP5
#print axioms S3115Donor
#print axioms S3115Donor_tensorUnit_ne_zero

end LeanFormal.IUT.XiFPaper.S3115CorrectedTensorDonorActualAdapted
end
