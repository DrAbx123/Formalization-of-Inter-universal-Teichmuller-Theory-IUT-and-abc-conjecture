# O4 Theta/Values candidate actual

## File
tmp/sheaf/n8/closure/O4ThetaCandidate.lean (compile EXIT=0, no sorry).

## Actual candidates (source objects, no new local readout)
- ActualThetaCandidate n := I.sourceSignedHullLogVolume D.place.v D.place.R n (production C9Native ThetaSigned).
- ActualQCandidate n := I.sourceSignedImageLogVolume D.place.v D.place.R n (production C9Native QSigned).
- ActualValuesCandidate n x := C9Native.Values D n x (production C4 witnessed-output signed values).

## Decisive results
- ActualQLeThetaCandidate is exactly C9Native.MissingSourceQHullComparison (Iff.rfl).
- ActualValuesBoundedCandidate is exactly C9Native.MissingValuesBoundedByTheta (Iff.rfl).
- Production proves only the reverse direction sourceSignedHullLogVolume <= sourceSignedImageLogVolume (hull contained in image union).

## No-go / missing source objects
1. Paper ellOut Theta needs an actual P6Readout / source output-region witness with ellOut. No actual P6Readout is constructed in production; the C9 output region/source-qualified output data (O1) is missing.
2. The needed Q <= Theta source direction is C9Native.MissingSourceQHullComparison; it is a named missing source comparison, not a free hypothesis.
3. The h <= Theta branch needs an actual C6 hull-unit -> source Theta identification; arithmeticTupleHullUnitLogVolume is a donor and no production theorem equates it with sourceSignedHullLogVolume.
4. ActualValuesBounded requires C9Native.MissingValuesBoundedByTheta over the full C4 witnessed-output family.

Therefore O4 is NOT closed by this branch: the actual Theta/Values source candidates are defined, but Q<=Theta, ValuesBounded and ellOut/hull alignment remain exact source gaps. No arbitrary object or local wrapper readout is introduced.
