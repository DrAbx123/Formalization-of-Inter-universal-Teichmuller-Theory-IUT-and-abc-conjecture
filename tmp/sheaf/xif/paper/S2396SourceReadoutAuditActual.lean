import tmp.sheaf.xif.paper.S2391QMarkReadoutActual

/-! # S2396: source readout audit

Audit of `SourceTheorem311Realization`, `BridgeOutput`, and `ActualOutput`:
- `SourceTheorem311Realization` carries procession/packet/vertical/evaluation
  data and `input`; its profile log-volume is `packet.logVolume` (`input_packet_volume`).
  It has no q-pilot scalar field.
- `BridgeOutput` carries `layers`, `reference`, `out`, `possibleOutputs`, and
  the explicit `qPilotAsOutput : C1SourceBridge`; it has no profile=q-pilot
  bridge field.
- `ActualOutput R = Theorem311Output R.input` carries three theorem parts and
  `source`; it has no q-pilot scalar field.

The only existing source compatibility equation in the tree
(`sourceProcessionRecordIntendedCarrierCard`) is
`C_T.profile.logVolume C_T.core.base = T.thetaPacket.logVolume`, i.e. a theta
packet comparison, not the q-pilot scalar.  Hence `profile.logVolume = sourceQPilotSignedLog`
is a paper-level C9 source input, recorded here exactly and not fabricated. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2396SourceReadoutAuditActual

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

/-- The realization profile is the packet log-volume; no q-pilot field is
involved. -/
theorem s2396_realization_profile_eq_packet (c : Choice) :
    R.input.profile.logVolume c = R.packet.logVolume c :=
  R.input_packet_volume c

/-- ActualOutput is the Theorem 3.11 output type. -/
theorem s2396_actualOutput_eq_output :
    ActualOutput R = Theorem311Output R.input :=
  rfl

/-- The BridgeOutput fields are the layer/reference outputs, the singleton
possible-output set, and the explicit q-pilot-as-output bridge. -/
theorem s2396_bridgeOutput_components
    (b : BridgeOutput (B := B) (R := R)) :
    b.out = b.layers.output ∧
      b.out = b.reference.output ∧
      b.possibleOutputs = Set.singleton b.out ∧
      b.qPilotAsOutput.qPilotOutput ∈ b.possibleOutputs :=
  ⟨b.out_eq_layers, b.out_eq_reference,
    b.possibleOutputs_eq, qPilot_mem_possibleOutputs b⟩

/-- Exact missing paper-level C9 source readout bridge: the actual profile
readout equals the source q-pilot scalar. -/
structure S2396ProfileQPilotBridgeRequired
    (b : BridgeOutput (B := B) (R := R)) where
  qPilotLogVolume : Real
  qPilot_eq : qPilotLogVolume = sourceQPilotSignedLog I.initial
  profile_readout_eq :
    R.input.profile.logVolume b.out.source = qPilotLogVolume

/-- The missing bridge yields the S2391 source readout datum. -/
noncomputable def s2396SourceReadoutOfBridge
    (b : BridgeOutput (B := B) (R := R))
    (E : S2396ProfileQPilotBridgeRequired b) :
    XiFPaper.S2391QMarkReadoutActual.S2391SourceReadoutRequired b :=
  { qPilotLogVolume := E.qPilotLogVolume
    qPilot_eq := E.qPilot_eq
    readout_eq := E.profile_readout_eq }

def S2396C9SourceInputRequired
    (b : BridgeOutput (B := B) (R := R)) : Prop :=
  Nonempty (S2396ProfileQPilotBridgeRequired b)

#check s2396_realization_profile_eq_packet
#check s2396_actualOutput_eq_output
#check s2396_bridgeOutput_components
#check S2396ProfileQPilotBridgeRequired
#check s2396SourceReadoutOfBridge
#check S2396C9SourceInputRequired

end LeanFormal.IUT.XiFPaper.S2396SourceReadoutAuditActual
end
