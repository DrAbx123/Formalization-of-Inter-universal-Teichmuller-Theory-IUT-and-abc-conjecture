import tmp.sheaf.xif.paper.MultiradialProcessionActual
import tmp.sheaf.xif.paper.IPLAPTActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1BPSIPLComponentConsumerActual
universe uG uv ua upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {A : CapsuleTheaterAssignment l V I}
variable {j : Fin (capsuleLevels l)}
variable {intermediateStrip gauStrip envStrip coricEnvStrip qPilotStrip : FPrimeStrip V}

theorem S3128Stage1BPSIPL_ofPerm_component
    (sigma : Capsule j.val ≃ Capsule j.val) (i : Capsule j.val) :
    (PrcAutomorphism.ofPerm A j sigma).component i =
      PrcTransition A j i (sigma i) := rfl

theorem S3128Stage1BPSIPL_ipl_factorization
    (L : IPLActual (G := G) intermediateStrip gauStrip envStrip coricEnvStrip
      qPilotStrip) :
    L.inputLink = L.composite :=
  L.inputLink_eq_composite

theorem S3128Stage1BPSIPL_ipl_inverse
    (L : IPLActual (G := G) intermediateStrip gauStrip envStrip coricEnvStrip
      qPilotStrip) :
    L.inverse = L.composite.symm := by
  rw [IPLActual.inverse_inputLink, IPLActual.inputLink_eq_composite]
  rfl

#check S3128Stage1BPSIPL_ofPerm_component
#check S3128Stage1BPSIPL_ipl_factorization
#check S3128Stage1BPSIPL_ipl_inverse
end LeanFormal.IUT.XiFPaper.S3128Stage1BPSIPLComponentConsumerActual