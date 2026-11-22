import tmp.sheaf.xif.paper.MultiradialProcessionActual
import tmp.sheaf.xif.paper.IPLAPTActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1BPSComponentConsumerActual
universe uG uv ua upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {A : CapsuleTheaterAssignment l V I}
variable {j : Fin (capsuleLevels l)} (i i' : Capsule j.val)
variable {intermediateStrip gauStrip envStrip coricEnvStrip qPilotStrip : FPrimeStrip V}
variable {L : IPLActual (G := G) intermediateStrip gauStrip envStrip coricEnvStrip qPilotStrip}

/-- BPS-carrier component consumer: actual procession member/transition and
the actual IPL link exposed as components, without asserting a BPS species. -/
structure S3128Stage1BPSComponentConsumerData where
  member : FPrimeStrip V
  member_eq : member = PrcMember A j i
  transition : FPrimeStripEquiv (PrcMember A j i) (PrcMember A j i')
  transition_eq : transition = PrcTransition A j i i'
  iplLink : FPrimeStripEquiv intermediateStrip qPilotStrip
  iplLink_eq : iplLink = L.inputLink

noncomputable def S3128Stage1BPSComponentConsumerData_ofCarriers :
    S3128Stage1BPSComponentConsumerData (i := i) (i' := i') (L := L) :=
  { member := PrcMember A j i
    member_eq := rfl
    transition := PrcTransition A j i i'
    transition_eq := rfl
    iplLink := L.inputLink
    iplLink_eq := rfl }

theorem S3128Stage1BPSComponentConsumer_transition_refl :
    PrcTransition A j i i = FPrimeStripEquiv.refl (PrcMember A j i) :=
  PrcTransition_refl A j i

theorem S3128Stage1BPSComponentConsumer_ipl_factorization :
    L.inputLink = L.composite :=
  L.inputLink_eq_composite

#check S3128Stage1BPSComponentConsumerData
#check S3128Stage1BPSComponentConsumerData_ofCarriers
#check S3128Stage1BPSComponentConsumer_transition_refl
#check S3128Stage1BPSComponentConsumer_ipl_factorization
end LeanFormal.IUT.XiFPaper.S3128Stage1BPSComponentConsumerActual