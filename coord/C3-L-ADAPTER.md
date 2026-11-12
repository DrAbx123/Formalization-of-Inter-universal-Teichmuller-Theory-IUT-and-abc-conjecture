# C3-L-ADAPTER — L-carrier C3 log-shell tensor packet (A978)

Status: GREEN LEAN ADAPTER. Source file:
tmp/sheaf/xif/paper/Mzk1C3LogShellTensorLActual.lean.
Compile EXIT=0, olean 272200 B.
SHA256 source 65FE0E94120A7E85F05FB0D13E74450A146F97FE8DB069180099B973C0CCEA02
SHA256 olean 9AA985F03D5130ABED297F053FE36B31431F9F22D627ABE3D8C774F19C665E6E
Gate: region_compact, Haar_isAddHaar, Haar_lt_top, packet all depend only on [propext, Classical.choice, Quot.sound].

## 1. What was adapted

Old: tmp/sheaf/xif/paper/C3LogShellTensorPacketActual.lean, parameter C3 : SourcePilotRegionData (old completion schema).
New: C3L : SourcePilotRegionDataL (S1391:244); actualSourcePilotRegionDataL is green.
The tensor block uses only p, hp, tensorIndex, tensorPlaces, tensorTuple; all exist verbatim in SourcePilotRegionDataL.
Definitions in Mzk1C3LogShellTensorLActual (all green):
- C3LogShellPlaceL (i) := C3L.tensorPlaces i (C3L.tensorTuple i);
- C3LogShellFiberL (i) := CommonPrimeCompletion (C3LogShellPlaceL i);
- C3LogShellTensorBlockL := ArithmeticTensorTupleBlock C3L.tensorPlaces C3L.tensorTuple;
- measurable/Borel/proper/locally-compact instances;
- actualC3LogShellDatumL (i) := sourceLocalLogShellDatum (p:=C3L.p) (place i);
- actualC3LogShellL (i) := datum.logShell;
- actualC3LogShellL_eq_integralLogShell (i);
- actualC3LogShellTensorRegionL := tensorIntegralRegion of actualC3LogShellL;
- actualC3LogShellTensorRegionL_compact;
- actualC3LogShellTensorIQL := Q-span of the region;
- actualC3LogShellTensorHaarL := Measure.addHaar;
- instance actualC3LogShellTensorHaarL_isAddHaar;
- actualC3LogShellTensorHaarL_lt_top (compactness => finite measure);
- actualC3LogShellTensorLogVolumeL := (haarLogVolume ...).toReal;
- structure ActualC3LogShellTensorPacketL and constructor actualC3LogShellTensorPacketL.

## 2. Field correspondence

| old C3 field | L record field | adapted? |
|---|---|---|
| p | p | exact |
| hp | hp | exact |
| tensorIndex | tensorIndex | exact |
| tensorFintype | tensorFintype | exact |
| tensorPlaceIndex | tensorPlaceIndex | exact |
| tensorPlaces | tensorPlaces | exact |
| tensorTuple | tensorTuple | exact |
| tensorUnit | tensorUnit | exact (available; unused by block) |
| tensorLanding | tensorLanding | exact (available; unused by block) |
| q/qUnit/roots/kummer | L q/qUnit/roots (alg closure) | not used by tensor block |

The old C3LogShellTensorBlock family adapts completely and definitionally for the tensor block/region/IQ/Haar/log-volume.

## 3. Basic lemmas proved

- region compact: actualC3LogShellTensorRegionL_compact;
- Haar is additive Haar: actualC3LogShellTensorHaarL_isAddHaar;
- region has finite Haar measure: actualC3LogShellTensorHaarL_lt_top;
- packet constructor with region/IQ/haar/log-volume equalities: actualC3LogShellTensorPacketL.
Not proved: strict positivity of Haar measure of the region (needs nonempty open/zero-interior argument; old C3 file also only proves compactness). The measure is AddHaar, so positivity holds for open nonempty sets; the tensor log-shell region is compact and may be lower-dimensional, so positivity is left as a gap.

## 4. Remaining gaps / scope

- This adapter removes the old SourcePilotRegionData dependency from the C3 tensor block.
- It does NOT provide a concrete C3L term: need a concrete I and place and an actual SourcePilotRegionDataL (actualSourcePilotRegionDataL needs I + place; I itself is a source obligation).
- L roots are algebraic-closure roots; the tensor block does not use them, so no mismatch here.
- The Haar log-volume is still a definition (toReal of haarLogVolume), not a numerical evaluation; computing R needs concrete C3L + normalization/evaluation lemmas.
- Old downstream consumers expecting C3LogShellTensorBlock C3 still need an L retype or adapter from old C3; this file gives the L analogue only.