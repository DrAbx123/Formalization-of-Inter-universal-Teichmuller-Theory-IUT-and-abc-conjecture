import tmp.sheaf.xif.paper.Ind2TensorActionActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.Ind2TensorActionActual
open scoped TensorProduct
namespace LeanFormal.IUT.XiFPaper.S3128Stage1Ind2SpecActual
universe ua uv upi umon ui uR uVQ uPlace uShell
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {R : Type uR} [CommSemiring R]
variable (C : SourceProcessionCapsuleContract R l V I)
variable (j : Fin (capsuleLevels l)) (vQ : C.VQ)

/-- Stage 1 Ind2 tensor-action consumer spec from actual Ind2TensorAction. -/
structure S3128Stage1Ind2Spec : Prop where
  factor_one :
    ∀ i : Capsule j.val,
      ind2FactorAction (C := C) (j := j) (vQ := vQ) 1 i =
        LinearEquiv.refl R (DirectSumFactor (C.logShell j) vQ i)
  factor_mul :
    ∀ (u v : Rˣ) (i : Capsule j.val),
      ind2FactorAction (C := C) (j := j) (vQ := vQ) (u * v) i =
        (ind2FactorAction (C := C) (j := j) (vQ := vQ) u i).trans
          (ind2FactorAction (C := C) (j := j) (vQ := vQ) v i)
  tensor_tprod :
    ∀ (f : Capsule j.val → Rˣ)
      (x : (i : Capsule j.val) → DirectSumFactor (C.logShell j) vQ i),
      ind2TensorEquiv (C := C) (j := j) (vQ := vQ) f
          (PiTensorProduct.tprod R x) =
        PiTensorProduct.tprod R
          (fun i =>
            ind2FactorAction (C := C) (j := j) (vQ := vQ) (f i) i (x i))

theorem S3128Stage1Ind2Spec_ofSource :
    S3128Stage1Ind2Spec (C := C) (j := j) (vQ := vQ) :=
  { factor_one := fun i => ind2FactorAction_one (C := C) (j := j) (vQ := vQ) i
    factor_mul := fun u v i =>
      ind2FactorAction_mul (C := C) (j := j) (vQ := vQ) u v i
    tensor_tprod := fun f x =>
      ind2TensorEquiv_tprod (C := C) (j := j) (vQ := vQ) f x }

#check S3128Stage1Ind2Spec
#check S3128Stage1Ind2Spec_ofSource
end LeanFormal.IUT.XiFPaper.S3128Stage1Ind2SpecActual