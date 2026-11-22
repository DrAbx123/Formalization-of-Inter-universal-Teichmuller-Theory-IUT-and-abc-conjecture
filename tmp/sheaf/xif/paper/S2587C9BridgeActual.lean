import tmp.sheaf.xif.paper.S2396SourceReadoutAuditActual
import tmp.sheaf.xif.paper.S2404QPilotArithmeticActual
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
namespace LeanFormal.IUT.XiFPaper.S2587C9BridgeActual
open LeanFormal.IUT.XiFPaper.S2396SourceReadoutAuditActual
open LeanFormal.IUT.XiFPaper.S2404QPilotArithmeticActual
/-- The S2396 profile-qPilot bridge, constructed from the S2404 arithmetic
identity (the remaining paper-level source input). -/
noncomputable def s2587BridgeOfIdentity
    (b : BridgeOutput (B := B) (R := R))
    (h : S2404QPilotProfileIdentity (I := I) b) :
    S2396ProfileQPilotBridgeRequired (I := I) b :=
  { qPilotLogVolume := sourceQPilotSignedLog I.initial
    qPilot_eq := rfl
    profile_readout_eq :=
      (s2404_candidate_eq_out (I := I) b).symm.trans h.symm }
/-- Exact obstruction: the S2396 bridge exists iff the S2404 arithmetic
identity holds for `b`. -/
theorem s2587BridgeRequired_iff_identity
    (b : BridgeOutput (B := B) (R := R)) :
    Nonempty (S2396ProfileQPilotBridgeRequired (I := I) b) ↔
      S2404QPilotProfileIdentity (I := I) b := by
  constructor
  · rintro ⟨E⟩
    unfold S2404QPilotProfileIdentity
    rw [s2404_candidate_eq_out (I := I) b]
    exact (E.profile_readout_eq.trans E.qPilot_eq).symm
  · intro h
    exact ⟨s2587BridgeOfIdentity (I := I) b h⟩
#check s2587BridgeOfIdentity
#check s2587BridgeRequired_iff_identity
end LeanFormal.IUT.XiFPaper.S2587C9BridgeActual
end
