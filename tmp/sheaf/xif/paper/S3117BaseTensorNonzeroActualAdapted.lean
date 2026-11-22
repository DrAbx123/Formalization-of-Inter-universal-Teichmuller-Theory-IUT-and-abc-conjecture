import tmp.sheaf.xif.paper.C3DonorUnconditionalActual
import tmp.sheaf.xif.paper.BasePlaceQCandidateActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.XiFPaper.C3DonorUnconditionalActual
open LeanFormal.IUT.XiFPaper.C3DonorFieldsFromSource
open LeanFormal.IUT.XiFPaper.BasePlaceQCandidateActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1600000

namespace LeanFormal.IUT.XiFPaper.S3117BaseTensorNonzeroActualAdapted

variable {l : PrimeGeFive} (X : N8NativeInput l)

local instance s3117PrimeFact : Fact (Nat.Prime (nativeC3Prime X)) := nativeC3PrimeFact X

abbrev S3117Index : Type := Unit
instance : Fintype S3117Index := inferInstance
abbrev S3117PlaceIndex : S3117Index -> Type := fun _ => Unit

def S3117Places : (i : S3117Index) -> S3117PlaceIndex i ->
    FinitePlaceAtPrime X.S.arithmetic.Fmod (nativeC3Prime X) :=
  fun _ _ => nativeC3Place X

def S3117Tuple : (i : S3117Index) -> S3117PlaceIndex i := fun _ => ()

abbrev S3117Block (X : N8NativeInput l) : Type := ArithmeticTensorTupleBlock (S3117Places X) S3117Tuple

noncomputable def S3117Insertion :
    CommonPrimeCompletion (nativeC3Place X) -> S3117Block X :=
  fun z => finitePadicTensorTprod (p := nativeC3Prime X)
    (M := fun _ : Unit => CommonPrimeCompletion (nativeC3Place X))
    (fun _ => z)

theorem S3117_insertion_ne_zero_aux
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
      (fun F : FinitePadicTensorIndex (p := p) (fun _ : Unit => M) -> ℚ_[p] =>
        F (fun _ : Unit => k)) hcoord
    simpa [finitePadicTensorCoordinates_tprod] using hk
  exact hx ((Module.finBasis ℚ_[p] M).repr.injective (by simpa using hrepr))

theorem S3117_insertion_ne_zero
    (q : FinitePlaceQCandidate (nativeC3Place X).val) (hq : q.q ≠ 0) :
    S3117Insertion X q.q ≠ 0 := by
  letI : NormedAddCommGroup (CommonPrimeCompletion (nativeC3Place X)) := inferInstance
  letI : NormedSpace ℚ_[nativeC3Prime X] (CommonPrimeCompletion (nativeC3Place X)) := inferInstance
  letI : FiniteDimensional ℚ_[nativeC3Prime X] (CommonPrimeCompletion (nativeC3Place X)) := inferInstance
  exact S3117_insertion_ne_zero_aux (p := nativeC3Prime X) q.q hq

theorem S3117_BaseTensorUnitNonzero
    (D : BaseQDescentData (X := X)) :
    S3117Insertion X (baseQCandidateOfDescent (X := X) D).q ≠ 0 :=
  S3117_insertion_ne_zero X (baseQCandidateOfDescent (X := X) D)
    (baseQCandidateOfDescent (X := X) D).q_ne_zero

#check S3117_insertion_ne_zero
#check S3117_BaseTensorUnitNonzero
#print axioms S3117_insertion_ne_zero
#print axioms S3117_BaseTensorUnitNonzero

end LeanFormal.IUT.XiFPaper.S3117BaseTensorNonzeroActualAdapted
end
