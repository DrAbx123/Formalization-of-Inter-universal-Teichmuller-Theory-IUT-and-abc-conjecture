import tmp.sheaf.xif.paper.S2362MainlineReadoutActual
import tmp.sheaf.n8.closure.C9IUTBridgeOutput

/-! # S2373: C1 readout from the actual C9 output profile

`U2K2` transports the q-mark, but the actual C9 output contract only gives the
reference output and its profile.  This file uses that actual output carrier and
profile readout: for `D = b.out`, `D` lies in the bridge possible-output set and
`nu_C(D)` is the actual profile log-volume.  The remaining equality
`nu_C(D) = Q_C` for the q-pilot scalar is recorded as the exact C1/xi-f gap.
No output or readout equality is fabricated. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2373C1ReadoutActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.C9IUTBridgeOutput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.S2362MainlineReadoutActual
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

/-- The actual profile log-volume of an actual Theorem 3.11 output. -/
def s2373Nu (R : SourceTheorem311Realization.{u, v, w} l Label Choice)
    (O : ActualOutput R) : Real :=
  R.input.profile.logVolume O.source

/-- The actual C9 output `b.out` lies in the bridge possible-output set and its
actual profile log-volume is its readout. -/
theorem s2373_actual_readout
    (b : BridgeOutput (B := B) (R := R)) :
    ∃ D : ActualOutput R,
      D ∈ b.possibleOutputs ∧ s2373Nu R D = s2373Nu R b.out := by
  exact ⟨b.out, out_mem_possibleOutputs b, rfl⟩

/-- Exact missing C1/xi-f equality: the actual output readout equals the
q-pilot scalar. -/
structure S2373QMarkReadoutEqRequired
    (b : BridgeOutput (B := B) (R := R)) where
  qPilotLogVolume : Real
  readout_eq : s2373Nu R b.out = qPilotLogVolume

/-- If the actual output readout equals the q-pilot scalar, the S2362 C1
projection is constructed using the actual C9 output carrier and profile readout. -/
noncomputable def s2373Projection
    {Xh : Type ux} {p : PaperSignedHull Xh Label} {F : S2362FixedCData p}
    (b : BridgeOutput (B := B) (R := R))
    (E : S2373QMarkReadoutEqRequired (B := B) b)
    (hQ : F.qPilotLogVolume = E.qPilotLogVolume) :
    S2362C1OutputReadoutProjectionRequired p F := by
  refine
    { Output := ActualOutput R
      P_C := b.possibleOutputs
      nu_C := s2373Nu R
      Q_C := F.qPilotLogVolume
      Q_C_eq_qPilot := rfl
      exists_output := ?_ }
  refine ⟨b.out, out_mem_possibleOutputs b, ?_⟩
  rw [E.readout_eq, ← hQ]

#check s2373Nu
#check s2373_actual_readout
#check S2373QMarkReadoutEqRequired
#check s2373Projection

end LeanFormal.IUT.XiFPaper.S2373C1ReadoutActual
end
