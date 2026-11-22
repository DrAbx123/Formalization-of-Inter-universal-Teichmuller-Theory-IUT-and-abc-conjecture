# C2 archimedean branch - stage 1 no-go

- Node: C2 child (archimedean branch).
- Owner: logdescent.
- Status: exact no-go; no local structure added.

Required: actual archimedean-place data for the source log-Kummer C2 object.

The current `SourceLogKummerData` and `C2Actual` are finite nonarchimedean
only: they range over `FinitePlaceAtPrime` and `CommonPrimeCompletion`.
`SourceInputBinding` supplies finite-place data; no archimedean source branch
is present.

Existing `archimedeanTargetLift` predicates in
`IUTIII/Theorem311/HullEnvelopeConditionsDischarge.lean` are conditional
reduction predicates for a frozen output, not actual archimedean source data.

Exact missing interface: actual archimedean source places and the corresponding
log-shell/log-Kummer data, plus their construction from C1/C3.  No such type
exists in C2/C1.  Not assumed, not added.