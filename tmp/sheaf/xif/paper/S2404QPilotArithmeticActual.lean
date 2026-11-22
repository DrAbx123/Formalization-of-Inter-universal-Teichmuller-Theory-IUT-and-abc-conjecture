import tmp.sheaf.xif.paper.S2401C1BridgeAuditActual

/-! # S2404: arithmetic form of the q-pilot readout gap

The C1 readout structure is equivalent to the single real identity
`sourceQPilotSignedLog I.initial = profile.logVolume b.qPilotAsOutput.qPilotOutput.source`.
The right-hand side is the actual candidate readout; the left-hand side is
`-sum_b |log q_b|`.  No existing profile/packet/theta-packet definition proves
this identity; it is recorded as the paper-level C9 arithmetic input. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2404QPilotArithmeticActual

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
variable {S : SourceP1P2Input (I := I) (R := R) (P := P)
  (X := X) (Y := Y) W}
variable {B : SourceP1P2Bundle W S}

/-- The actual candidate q-pilot readout from the C1 q-pilot output. -/
def s2404CandidateQPilotLogVolume
    (b : BridgeOutput (B := B) (R := R)) : Real :=
  R.input.profile.logVolume b.qPilotAsOutput.qPilotOutput.source

theorem s2404_candidate_eq_out
    (b : BridgeOutput (B := B) (R := R)) :
    s2404CandidateQPilotLogVolume b =
      R.input.profile.logVolume b.out.source :=
  XiFPaper.S2401C1BridgeAuditActual.s2401_qPilotOutput_profile_eq b

/-- The source q-pilot scalar is the negative bad-q absolute log sum. -/
theorem s2404_sourceQPilot_eq_neg_sum :
    sourceQPilotSignedLog I.initial = -sourceBadQAbsLog I.initial :=
  rfl

/-- The arithmetic identity underlying the C1 readout structure. -/
def S2404QPilotProfileIdentity
    (b : BridgeOutput (B := B) (R := R)) : Prop :=
  sourceQPilotSignedLog I.initial = s2404CandidateQPilotLogVolume b

theorem s2404_candidate_eq_packet
    (b : BridgeOutput (B := B) (R := R)) :
    s2404CandidateQPilotLogVolume b =
      R.packet.logVolume b.out.source := by
  rw [s2404_candidate_eq_out,
    XiFPaper.S2396SourceReadoutAuditActual.s2396_realization_profile_eq_packet]

/-- The arithmetic gap is exactly packet log-volume vs source q-pilot sum. -/
theorem s2404_identity_iff_packet
    (b : BridgeOutput (B := B) (R := R)) :
    S2404QPilotProfileIdentity b ↔
      sourceQPilotSignedLog I.initial =
        R.packet.logVolume b.out.source := by
  rw [S2404QPilotProfileIdentity, s2404_candidate_eq_packet]


/-- The C1 readout structure is exactly the arithmetic identity. -/
theorem s2404_readoutRequired_iff_identity
    (b : BridgeOutput (B := B) (R := R)) :
    Nonempty
        (XiFPaper.S2401C1BridgeAuditActual.S2401QPilotOutputReadoutRequired b) ↔
      S2404QPilotProfileIdentity b := by
  constructor
  · rintro ⟨⟨q, hq, hr⟩⟩
    change sourceQPilotSignedLog I.initial =
      s2404CandidateQPilotLogVolume b
    rw [← hq]
    exact hr.symm
  · intro h
    exact ⟨{ qPilotLogVolume := s2404CandidateQPilotLogVolume b
             qPilot_eq := h.symm
             readout_eq := rfl }⟩

/-- The identity gives the S2401 readout datum. -/
noncomputable def s2404ReadoutOfIdentity
    (b : BridgeOutput (B := B) (R := R))
    (h : S2404QPilotProfileIdentity b) :
    XiFPaper.S2401C1BridgeAuditActual.S2401QPilotOutputReadoutRequired b :=
  { qPilotLogVolume := s2404CandidateQPilotLogVolume b
    qPilot_eq := h.symm
    readout_eq := rfl }

/-- Exact paper-level arithmetic input: the q-pilot scalar equals the actual
candidate profile readout. -/
structure S2404QPilotArithmeticRequired
    (b : BridgeOutput (B := B) (R := R)) where
  arithmetic_identity : S2404QPilotProfileIdentity b

def S2404QPilotArithmeticRequiredProp : Prop :=
  ∀ (b : BridgeOutput (B := B) (R := R)),
    Nonempty (S2404QPilotArithmeticRequired b)

#check s2404CandidateQPilotLogVolume
#check s2404_candidate_eq_out
#check s2404_sourceQPilot_eq_neg_sum
#check S2404QPilotProfileIdentity
#check s2404_readoutRequired_iff_identity
#check s2404ReadoutOfIdentity
#check S2404QPilotArithmeticRequired
#check S2404QPilotArithmeticRequiredProp

end LeanFormal.IUT.XiFPaper.S2404QPilotArithmeticActual
end
