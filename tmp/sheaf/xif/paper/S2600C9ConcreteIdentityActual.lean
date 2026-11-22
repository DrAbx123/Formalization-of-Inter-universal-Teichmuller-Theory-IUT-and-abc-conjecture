import tmp.sheaf.xif.paper.S2451ProcessionAverageActual
import tmp.sheaf.xif.paper.S2589S2404IdentityReductionActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.C9IUTBridgeOutput
open LeanFormal.IUT.XiFPaper
open OriginalInput
open SourceHodgeTheaterBridge

namespace LeanFormal.IUT.XiFPaper.S2600C9ConcreteIdentityActual

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

/-- The concrete S1895/S2451 q-pilot scalar is the source signed q-pilot log. -/
theorem s2600_paperQPilot_eq_source (D : LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual.S1895PaperInput) :
    LeanFormal.IUT.XiFPaper.S1968QVDeterminedQPilotActual.paperQPilotLogVolume D =
      sourceQPilotSignedLog (LeanFormal.IUT.XiFPaper.S1960QPilotAnchorActual.paperInput D).initial :=
  LeanFormal.IUT.XiFPaper.S2451ProcessionAverageActual.s2451_qPilotLogVolume_eq_source D

end LeanFormal.IUT.XiFPaper.S2600C9ConcreteIdentityActual

end