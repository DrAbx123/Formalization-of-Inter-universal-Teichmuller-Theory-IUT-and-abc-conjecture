import tmp.sheaf.xif.paper.PrimeStripLogShellActual
import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual

/-! # Actual projections of the prime-strip capsule and the C3 tensor packet

IUT III, Proposition 3.2, (i), (ii), pp. 97-99.  This file records the actual
projection and compatibility data of the source D-/F-prime-strip capsule
constructed in PrimeStripLogShellActual, together with the actual projection
data of the C3 tensor packet of log-shells constructed in
C3LogShellTensorPacketActual.

The F-strip projections are the actual prime-strip fields (value monoid,
projection, action, degree, mono-analytic group).  The D-strip projection is
the actual forgetful image, with the proved equality dStrip = fStrip.toD.
The C3 packet projections are the actual tensor block, log-shell region,
IQ carrier, Haar measure and Haar log-volume.

No index comparison V = C3.tensorIndex is used.  No inequality is judged. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PrimeStripProjectionActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open MeasureTheory

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [forall i, Fintype (C3.tensorPlaceIndex i)]

/-- The actual prime-strip capsule projection data, directly from the actual
source theater. -/
abbrev capsuleFStrip : FPrimeStrip.{umon, uv, upi} V :=
  (actualDFPrimeStripCapsule (V := V) (I := I)).fStrip

/-- The actual D-strip projection. -/
abbrev capsuleDStrip : DPrimeStrip.{upi, uv} V :=
  (actualDFPrimeStripCapsule (V := V) (I := I)).dStrip

/-- The D-strip is the actual forgetful image of the F-strip. -/
theorem capsuleDStrip_eq_toD :
    capsuleDStrip (V := V) (I := I) =
      (capsuleFStrip (V := V) (I := I)).toDPrimeStrip :=
  (actualDFPrimeStripCapsule (V := V) (I := I)).dStrip_eq

/-- The actual value monoid at a source place. -/
def capsuleMon (v : V) : Type umon :=
  (capsuleFStrip (V := V) (I := I)).Mon v

/-- The actual projection Pi_v -> G_v. -/
def capsuleProj (v : V) :
    (capsuleFStrip (V := V) (I := I)).toDPrimeStrip.Pi v →*
      (capsuleFStrip (V := V) (I := I)).G v :=
  (capsuleFStrip (V := V) (I := I)).proj v

/-- The actual projection is the D-strip projection. -/
theorem capsuleProj_eq_dStrip (v : V) :
    capsuleProj (V := V) (I := I) v =
      (capsuleDStrip (V := V) (I := I)).proj v := rfl

/-- The actual action of Pi_v on the value monoid. -/
def capsuleAction (v : V) :
    (capsuleFStrip (V := V) (I := I)).toDPrimeStrip.Pi v →*
      MulAut (capsuleMon (V := V) (I := I) v) :=
  (capsuleFStrip (V := V) (I := I)).action v

/-- The actual degree map of the value monoid. -/
def capsuleDegree (v : V) :
    capsuleMon (V := V) (I := I) v →* Multiplicative Real :=
  (capsuleFStrip (V := V) (I := I)).degree v

/-- The actual mono-analytic group projection. -/
def capsuleMonoAnalytic (v : V) : Type upi :=
  (capsuleFStrip (V := V) (I := I)).monoAnalytic v

/-- The actual geometric kernel of the projection. -/
def capsuleGeometric (v : V) :
    Subgroup ((capsuleFStrip (V := V) (I := I)).toDPrimeStrip.Pi v) :=
  (capsuleDStrip (V := V) (I := I)).geometric v

/-- The actual C3 tensor packet projections: block, region, IQ carrier, Haar
measure and Haar log-volume. -/
structure C3TensorPacketProjectionData where
  block : Type
  block_eq : block = (actualC3LogShellTensorPacket (I := I) C3).block
  region : Set block
  region_eq : region = (actualC3LogShellTensorPacket (I := I) C3).region
  iqCarrier : Submodule ℚ block
  iqCarrier_eq : iqCarrier = (actualC3LogShellTensorPacket (I := I) C3).iqCarrier
  haar : Measure block
  haar_eq : haar = (actualC3LogShellTensorPacket (I := I) C3).haar
  logVolume : Real
  logVolume_eq : logVolume = (actualC3LogShellTensorPacket (I := I) C3).logVolume

/-- The actual C3 tensor packet projection data. -/
noncomputable def c3TensorPacketProjectionData :
    C3TensorPacketProjectionData (I := I) C3 where
  block := (actualC3LogShellTensorPacket (I := I) C3).block
  block_eq := rfl
  region := (actualC3LogShellTensorPacket (I := I) C3).region
  region_eq := rfl
  iqCarrier := (actualC3LogShellTensorPacket (I := I) C3).iqCarrier
  iqCarrier_eq := rfl
  haar := (actualC3LogShellTensorPacket (I := I) C3).haar
  haar_eq := rfl
  logVolume := (actualC3LogShellTensorPacket (I := I) C3).logVolume
  logVolume_eq := rfl

end LeanFormal.IUT.XiFPaper.PrimeStripProjectionActual

end
