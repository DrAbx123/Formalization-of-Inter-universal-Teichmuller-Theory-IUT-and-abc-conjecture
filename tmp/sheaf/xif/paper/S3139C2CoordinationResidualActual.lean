/-!
# S3139: C2 coordination record and reduced residual ownership (component documentation)

Coordination results for C2 (finite-place conjugate channel, IUT III:616-620,
Fig. I.5), as answered by the owning streams:

* shehdd (S3134 chain): NO constructed placeToMod-type map from the paper place
  set to the actual @F_mod@ places; the paper @placeToMod@ record projection is
  the genuine source missing recorded in
  SourceDefinition31DualContractAlignment.lean:88.  The native-side data they
  expose (nativePlaceSelection, nativeBadToKPlace, localCompletionDegree,
  S3134CuspEpsilonReal, S3134QParameter) are completion-degree / real-valued
  readouts only, not global-to-local element maps.
* stage4 (S3136 LGP actuals): local unit groups at fibers exist
  ((AlgebraicClosure (Completion (qVPlace T b)))^x and the C3 tensor places
  (C3LogShellFiber C3 i)^x), and a canonical global-units map is constructible
  from the actual algebra structure
  (LeanFormal.IUT.NumberFieldFinitePlace.normalizedCompletionAlgebra):
  Units.map (algebraMap Fmod (NormalizedCompletion place)).  stage4 is adding
  S3136LGPGlobalUnitsToLocalUnitsActual with lgpGlobalUnitsToLocalUnits.
  Their remaining missing data are exactly (a) the same-C identification
  F ~ Fmod (M0/R1) and (b) the place selection V -> C3.tensorIndex
  (c3LogShellPlace, M1) — both already owned by lattice/mainline/qpilot.

## Consequence for the C2 residual

With the completion-level candidates constructed in this stream
(@S3139C2FiniteCompletionUnitsActual@, @S3139C2InfiniteCompletionUnitsActual@)
and the realified degree/scalar channel reduction
(@S3139C2LocalDegreeDataActual@), C2 is NOT independent missing data: it reduces
to the already-owned identifications (a) same-C model identification (M0/R1) and
(b) the place selection (M1), plus the actual local log degree readout of the
completion units.  The exact remaining record is:

* @S3139C2LocalDegreeDataActual.SourceFmodLocalElementMap@: filled once stage4's
  lgpGlobalUnitsToLocalUnits is composed with the (a)/(b) identifications and
  the local realified degree;
* @S3139C2FiniteCopyActionActual.SourceCapsuleFiberAssignment@: filled by the
  same place selection (M1, qpilot place-index files).

Owner after coordination: qpilot/index files for (b) (S3133BadToAllPlaceIndex-
InjectionActual / S3131BadTensorIndexEquivalence), lattice/mainline for (a)
(M0/R1 same-C identification), stage4 for the global-units-to-local-units unit
map; stepxi for the downstream degree/scalar and copy-action assembly (this
stream).  No contract change; no edits to other streams' files.
-/
