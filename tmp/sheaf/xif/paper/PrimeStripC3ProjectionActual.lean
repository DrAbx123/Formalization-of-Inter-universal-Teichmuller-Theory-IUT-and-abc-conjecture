import tmp.sheaf.xif.paper.PrimeStripC3LogShellCapsuleActual
import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual

/-! # Actual projections between the source prime-strip capsule and the C3 packet

Q2/Q7 actual projection data.  The paired object
ActualPrimeStripC3LogShellObject carries the actual source F/D-prime-strip
capsule and the actual C3-indexed log-shell data.  This file constructs the
actual projections of that paired object to:

* the source F/D-prime-strip capsule (fStrip, dStrip, dStrip = fStrip.toD);
* the actual C3 log-shell tensor packet (block, region, IQ carrier, Haar
  measure, Haar log-volume).

The projections are actual functions/structures built from the paired object;
no index comparison V = C3.tensorIndex is asserted.  No inequality is judged.
No sorry, axiom, True, or PUnit is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PrimeStripC3ProjectionActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual
open LeanFormal.IUT.XiFPaper.PrimeStripC3LogShellCapsuleActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open MeasureTheory

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [forall i, Fintype (C3.tensorPlaceIndex i)]

/-- Actual projection: the paired object's source F-prime-strip. -/
def pairedSourceFStrip :
    FPrimeStrip.{umon, uv, upi} V :=
  (actualPrimeStripC3LogShellObject (V := V) (I := I) C3).fStrip

/-- Actual projection: the paired object's source D-prime-strip. -/
def pairedSourceDStrip :
    DPrimeStrip.{upi, uv} V :=
  (actualPrimeStripC3LogShellObject (V := V) (I := I) C3).dStrip

/-- Actual projection equality: the source D-strip is the forgetful image. -/
theorem pairedSourceDStrip_eq_toD :
    pairedSourceDStrip (V := V) (I := I) C3 =
      (pairedSourceFStrip (V := V) (I := I) C3).toDPrimeStrip :=
  (actualPrimeStripC3LogShellObject (V := V) (I := I) C3).dStrip_eq

/-- Actual projection: the paired object's C3 log-shell datum at i. -/
def pairedC3LogShellDatum (i : C3.tensorIndex) : SourceLogShellDatum :=
  (actualPrimeStripC3LogShellObject (V := V) (I := I) C3).c3LogShellDatum i

/-- Actual projection: the paired object's C3 log-shell at i. -/
def pairedC3LogShell (i : C3.tensorIndex) :
    Set (CommonPrimeCompletion (c3LogShellPlace C3 i)) :=
  (actualPrimeStripC3LogShellObject (V := V) (I := I) C3).c3LogShell i

/-- The paired C3 log-shell is the actual C3 local log-shell. -/
theorem pairedC3LogShell_eq_actual (i : C3.tensorIndex) :
    pairedC3LogShell (V := V) (I := I) C3 i =
      actualC3LogShell (I := I) C3 i := rfl

/-- Actual projection: the C3 tensor packet built from the paired object's
actual C3-indexed log-shell data. -/
noncomputable def pairedC3TensorPacket :
    ActualC3LogShellTensorPacket (I := I) C3 :=
  actualC3LogShellTensorPacket (I := I) C3

/-- Actual projection equality: the projected C3 tensor packet is the actual
C3 packet constructed from the C3 tensor places/log-shells. -/
theorem pairedC3TensorPacket_eq :
    pairedC3TensorPacket (I := I) C3 =
      actualC3LogShellTensorPacket (I := I) C3 := rfl

/-- Actual projection data: source prime-strip capsule plus C3 tensor packet,
with their actual projection equalities. -/
structure ActualPrimeStripC3ProjectionData where
  sourceFStrip : FPrimeStrip.{umon, uv, upi} V
  sourceDStrip : DPrimeStrip.{upi, uv} V
  sourceDStrip_eq_toD : sourceDStrip = sourceFStrip.toDPrimeStrip
  c3Packet : ActualC3LogShellTensorPacket (I := I) C3
  c3Packet_eq : c3Packet = actualC3LogShellTensorPacket (I := I) C3

/-- The actual projection data from the paired capsule/packet object. -/
noncomputable def actualPrimeStripC3ProjectionData :
    ActualPrimeStripC3ProjectionData (V := V) (I := I) C3 where
  sourceFStrip := pairedSourceFStrip (V := V) (I := I) C3
  sourceDStrip := pairedSourceDStrip (V := V) (I := I) C3
  sourceDStrip_eq_toD := pairedSourceDStrip_eq_toD (V := V) (I := I) C3
  c3Packet := pairedC3TensorPacket (I := I) C3
  c3Packet_eq := pairedC3TensorPacket_eq (I := I) C3

end LeanFormal.IUT.XiFPaper.PrimeStripC3ProjectionActual

end
