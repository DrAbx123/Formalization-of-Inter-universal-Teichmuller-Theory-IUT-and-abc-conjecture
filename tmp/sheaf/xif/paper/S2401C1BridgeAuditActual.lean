import tmp.sheaf.xif.paper.S2396SourceReadoutAuditActual

/-! # S2401: C1SourceBridge/qPilotAsOutput audit

`C1SourceBridge` only asserts that `qPilotAsOutput.qPilotOutput` lies in the
bridge possible-output set.  In `BridgeOutput` that set is the singleton
`{b.out}`, so the q-pilot output is forced to be `b.out` and its profile
log-volume is `profile.logVolume b.out.source`.  This is a genuine relation,
but it does not identify that profile value with `sourceQPilotSignedLog`; the
source scalar remains the paper-level C9 input. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2401C1BridgeAuditActual

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

/-- The C1 q-pilot output is forced to be the bridge output by singleton membership. -/
theorem s2401_qPilotOutput_eq_out
    (b : BridgeOutput (B := B) (R := R)) :
    b.qPilotAsOutput.qPilotOutput = b.out := by
  let q := b.qPilotAsOutput.qPilotOutput
  have hmem : q ∈ b.possibleOutputs := b.qPilotAsOutput.qPilotOutput_mem
  have hsing : b.possibleOutputs = Set.singleton b.out := by
    rw [b.possibleOutputs_eq]
    rfl
  have hmem' : q ∈ Set.singleton b.out := by
    simpa [hsing] using hmem
  have hq : q = b.out := Set.mem_singleton_iff.mp hmem'
  show b.qPilotAsOutput.qPilotOutput = b.out
  exact hq

/-- Consequently the q-pilot output has exactly the bridge output's profile readout. -/
theorem s2401_qPilotOutput_profile_eq
    (b : BridgeOutput (B := B) (R := R)) :
    R.input.profile.logVolume b.qPilotAsOutput.qPilotOutput.source =
      R.input.profile.logVolume b.out.source := by
  rw [s2401_qPilotOutput_eq_out b]

/-- The source scalar definition is the negative bad-q absolute log sum. -/
theorem s2401_sourceQPilot_def :
    sourceQPilotSignedLog I.initial = -sourceBadQAbsLog I.initial :=
  rfl

/-- Exact paper-level C1 readout interface on the q-pilot output itself. -/
structure S2401QPilotOutputReadoutRequired
    (b : BridgeOutput (B := B) (R := R)) where
  qPilotLogVolume : Real
  qPilot_eq : qPilotLogVolume = sourceQPilotSignedLog I.initial
  readout_eq :
    R.input.profile.logVolume b.qPilotAsOutput.qPilotOutput.source =
      qPilotLogVolume

/-- The C1 interface yields the S2396 profile-qPilot bridge. -/
noncomputable def s2401BridgeOfQPilotOutput
    (b : BridgeOutput (B := B) (R := R))
    (E : S2401QPilotOutputReadoutRequired b) :
    XiFPaper.S2396SourceReadoutAuditActual.S2396ProfileQPilotBridgeRequired b :=
  { qPilotLogVolume := E.qPilotLogVolume
    qPilot_eq := E.qPilot_eq
    profile_readout_eq :=
      (s2401_qPilotOutput_profile_eq b).symm.trans E.readout_eq }

def S2401C1ReadoutRequired : Prop :=
  ∀ (b : BridgeOutput (B := B) (R := R)),
    Nonempty (S2401QPilotOutputReadoutRequired b)

#check s2401_qPilotOutput_eq_out
#check s2401_qPilotOutput_profile_eq
#check s2401_sourceQPilot_def
#check S2401QPilotOutputReadoutRequired
#check s2401BridgeOfQPilotOutput
#check S2401C1ReadoutRequired

end LeanFormal.IUT.XiFPaper.S2401C1BridgeAuditActual
end
