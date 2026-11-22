import tmp.sheaf.xif.paper.S2373C1ReadoutActual
import tmp.sheaf.xif.PaperQPilotObject

/-! # S2391: q-mark readout equality from definitions

The C9 actual output profile readout unfolds definitionally to
`R.input.profile.logVolume b.out.source`, and the output source is the source
choice `R.input.core.base`.  The q-pilot scalar is
`sourceQPilotSignedLog I.initial`, an independent source sum.  No definitional
identity identifies the two; the exact missing C9 source readout projection is
recorded as an explicit structure with no inhabitant. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2391QMarkReadoutActual

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

theorem s2391_readout_unfold
    (b : BridgeOutput (B := B) (R := R)) :
    XiFPaper.S2373C1ReadoutActual.s2373Nu R b.out =
      R.input.profile.logVolume b.out.source :=
  rfl

theorem s2391_out_source_eq_base
    (b : BridgeOutput (B := B) (R := R)) :
    b.out.source = R.input.core.base :=
  b.out.source_eq

/-- The exact C9 source readout projection gap, in source-scalar form. -/
structure S2391SourceReadoutRequired
    (b : BridgeOutput (B := B) (R := R)) where
  qPilotLogVolume : Real
  qPilot_eq : qPilotLogVolume = sourceQPilotSignedLog I.initial
  readout_eq : R.input.profile.logVolume b.out.source = qPilotLogVolume

/-- If the actual profile readout equals the source q-pilot scalar, the S2373
readout equality holds. -/
noncomputable def s2391QMarkReadoutEqOfSourceEq
    (b : BridgeOutput (B := B) (R := R))
    (h : R.input.profile.logVolume b.out.source =
      sourceQPilotSignedLog I.initial) :
    XiFPaper.S2373C1ReadoutActual.S2373QMarkReadoutEqRequired b where
  qPilotLogVolume := sourceQPilotSignedLog I.initial
  readout_eq := (s2391_readout_unfold b).trans h

/-- Conditional C1 projection from the profile-q-pilot equality. -/
noncomputable def s2391ProjectionOfSourceEq
    {Xh : Type ux} {p : PaperSignedHull Xh Label}
    {F : XiFPaper.S2362MainlineReadoutActual.S2362FixedCData p}
    (b : BridgeOutput (B := B) (R := R))
    (h : R.input.profile.logVolume b.out.source =
      sourceQPilotSignedLog I.initial)
    (hQ : F.qPilotLogVolume = sourceQPilotSignedLog I.initial) :
    XiFPaper.S2362MainlineReadoutActual.S2362C1OutputReadoutProjectionRequired p F :=
  XiFPaper.S2373C1ReadoutActual.s2373Projection b
    (s2391QMarkReadoutEqOfSourceEq b h) hQ

#check s2391_readout_unfold
#check s2391_out_source_eq_base
#check S2391SourceReadoutRequired
#check s2391QMarkReadoutEqOfSourceEq
#check s2391ProjectionOfSourceEq

end LeanFormal.IUT.XiFPaper.S2391QMarkReadoutActual
end
