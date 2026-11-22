import tmp.sheaf.xif.paper.S3128Stage1Ind2SpecActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.Ind2TensorActionActual
open LeanFormal.IUT.XiFPaper.S3128Stage1Ind2SpecActual
open scoped TensorProduct
namespace LeanFormal.IUT.XiFPaper.S3128Stage1Ind2DownstreamActual
universe ua uv upi umon ui uR uVQ uPlace uShell
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {R : Type uR} [CommSemiring R]
variable (C : SourceProcessionCapsuleContract R l V I)
variable (j : Fin (capsuleLevels l)) (vQ : C.VQ)

theorem S3128Stage1Ind2Downstream_factor_one
    (i : Capsule j.val) :
    ind2FactorAction (C := C) (j := j) (vQ := vQ) 1 i =
      LinearEquiv.refl R (DirectSumFactor (C.logShell j) vQ i) :=
  (S3128Stage1Ind2Spec_ofSource (C := C) (j := j) (vQ := vQ)).factor_one i

theorem S3128Stage1Ind2Downstream_factor_mul
    (u v : Rˣ) (i : Capsule j.val) :
    ind2FactorAction (C := C) (j := j) (vQ := vQ) (u * v) i =
      (ind2FactorAction (C := C) (j := j) (vQ := vQ) u i).trans
        (ind2FactorAction (C := C) (j := j) (vQ := vQ) v i) :=
  (S3128Stage1Ind2Spec_ofSource (C := C) (j := j) (vQ := vQ)).factor_mul u v i

theorem S3128Stage1Ind2Downstream_tensor_tprod
    (f : Capsule j.val → Rˣ)
    (x : (i : Capsule j.val) → DirectSumFactor (C.logShell j) vQ i) :
    ind2TensorEquiv (C := C) (j := j) (vQ := vQ) f
        (PiTensorProduct.tprod R x) =
      PiTensorProduct.tprod R
        (fun i =>
          ind2FactorAction (C := C) (j := j) (vQ := vQ) (f i) i (x i)) :=
  (S3128Stage1Ind2Spec_ofSource (C := C) (j := j) (vQ := vQ)).tensor_tprod f x

#check S3128Stage1Ind2Downstream_factor_one
#check S3128Stage1Ind2Downstream_factor_mul
#check S3128Stage1Ind2Downstream_tensor_tprod
end LeanFormal.IUT.XiFPaper.S3128Stage1Ind2DownstreamActual