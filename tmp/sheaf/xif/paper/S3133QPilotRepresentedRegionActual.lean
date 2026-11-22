import tmp.sheaf.xif.paper.S3133QPilotOneColumnRegionCarrierActual
import tmp.sheaf.xif.paper.S3133QPilotOneColumnRegionActual

/-!
# Represented q-pilot region on 1,circ U_Q: module index / parked tensor-unit route

Actual 1,circ U_Q carrier, region, Haar measure, dimension, packet normalization
and p-scaled region are constructed in S3133QPilotOneColumnRegionCarrierActual;
the actual region object, lattice/mainline alignment and the field-level exact
MissingQPilotOneColumnReading (placeComparison, qActionIdentification,
weightNormalization, readingIdentification) are in
S3133QPilotOneColumnRegionActual.

PARKED route (not constructed): representing the q-pilot object directly by
multiplying the 1,circ U region by the actual C3 tensor unit qPilotTensorUnit
(C3.tensorUnit, the image of the actual completion q under the actual C3 tensor
landing C3.tensorLanding_q).  The naive definition
  (C3.tensorUnit : C3LogShellTensorBlock C3) • 1,circ U region
requires the actual smul/multiplication and Haar scaling instances for the
p-adic tensor block, whose instance search times out on the product carrier;
this is recorded as part of the qActionIdentification slot of
MissingQPilotOneColumnReading and no arbitrary carrier is substituted here.
No sorry/axiom/toy.  WRITE-ONLY.
-/
