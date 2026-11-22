import tmp.sheaf.xif.paper.MultiradialProcessionActual
import tmp.sheaf.xif.paper.IPLAPTActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1BPSAutConsumerActual
universe uG uv ua upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {A : CapsuleTheaterAssignment l V I}
variable {j : Fin (capsuleLevels l)}

theorem S3128Stage1BPSAut_perm
    (sigma : Capsule j.val ≃ Capsule j.val) :
    (PrcAutomorphism.ofPerm A j sigma).perm = sigma := rfl

theorem S3128Stage1BPSAut_comp_perm
    (sigma tau : PrcAutomorphism A j) :
    (PrcAutomorphism.comp A j sigma tau).perm =
      sigma.perm.trans tau.perm := rfl

theorem S3128Stage1BPSAut_id_perm :
    (PrcAutomorphism.id A j).perm =
      Equiv.refl (Capsule j.val) := rfl

#check S3128Stage1BPSAut_perm
#check S3128Stage1BPSAut_comp_perm
#check S3128Stage1BPSAut_id_perm
end LeanFormal.IUT.XiFPaper.S3128Stage1BPSAutConsumerActual