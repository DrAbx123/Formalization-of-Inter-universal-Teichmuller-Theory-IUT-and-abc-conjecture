import tmp.sheaf.xif.paper.MultiradialProcessionActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
namespace LeanFormal.IUT.XiFPaper.S3128Ind1InterfaceActual
universe ua uv upi umon ui uR uVQ uPlace uShell
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {R : Type uR} [CommSemiring R]
variable (C : SourceProcessionCapsuleContract R l V I)
variable (j : Fin (capsuleLevels l)) (vQ : C.VQ)

theorem Ind1TensorAction_eq_tensorMap :
    Ind1TensorAction C j vQ = (C.polyIso j).tensorMap vQ := rfl

theorem Ind1TensorAction_apply
    (x : ActualTensorPacket C j vQ) :
    Ind1TensorAction C j vQ x = (C.polyIso j).tensorMap vQ x := rfl

#check Ind1TensorAction_eq_tensorMap
#check Ind1TensorAction_apply
end LeanFormal.IUT.XiFPaper.S3128Ind1InterfaceActual