import tmp.sheaf.xif.paper.S2404QPilotArithmeticActual
import tmp.sheaf.xif.paper.S2396SourceReadoutAuditActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.C9IUTBridgeOutput
open LeanFormal.IUT.XiFPaper
open OriginalInput
open SourceHodgeTheaterBridge
universe u v w uv upi umon ui ux uy
variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{u, uv, upi, umon, ui} l V}
variable {R : SourceTheorem311Realization.{u, v, w} l Label Choice}
variable {P : H2SpokePermutation I}
variable {X : Type ux} {Y : Type uy}
variable [CommMonoid X] [CommMonoid Y]
variable [Fintype Label]
variable {W : SourceInternalWiring I R P X Y}
variable {S : SourceP1P2Input (I := I) (R := R) (P := P) (X := X) (Y := Y) W}
variable {B : SourceP1P2Bundle W S}
namespace LeanFormal.IUT.XiFPaper.S2589S2404IdentityReductionActual
open LeanFormal.IUT.XiFPaper.S2396SourceReadoutAuditActual
open LeanFormal.IUT.XiFPaper.S2404QPilotArithmeticActual
/-- The S2404 identity is exactly the packet log-volume identity after
the actual S2396 profile=packet reduction. -/
theorem s2589_identity_iff_packet
    (b : BridgeOutput (B := B) (R := R)) :
    S2404QPilotProfileIdentity (I := I) b ↔
      R.packet.logVolume b.out.source = sourceQPilotSignedLog I.initial := by
  constructor
  · intro h
    have hcand : s2404CandidateQPilotLogVolume (I := I) b =
        R.packet.logVolume b.out.source := s2404_candidate_eq_packet (I := I) b
    exact hcand.symm.trans h.symm
  · intro h
    unfold S2404QPilotProfileIdentity
    exact ((s2404_candidate_eq_packet (I := I) b).trans h).symm
/-- Equivalent form: packet log-volume equals the negative bad-q absolute log. -/
theorem s2589_identity_iff_badQ
    (b : BridgeOutput (B := B) (R := R)) :
    S2404QPilotProfileIdentity (I := I) b ↔
      R.packet.logVolume b.out.source = -sourceBadQAbsLog I.initial := by
  rw [s2589_identity_iff_packet (I := I) b, s2404_sourceQPilot_eq_neg_sum]
#check s2589_identity_iff_packet
#check s2589_identity_iff_badQ
end LeanFormal.IUT.XiFPaper.S2589S2404IdentityReductionActual
end
