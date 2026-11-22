# F-level Rss alignment: carrier equality + exact quotient bridge target

- Task: align multiradial FLevelRss/qOClass/openClassF/closedClassF with
  GlobalRssAtF/global classes.
- Owner: logdescent.
- Lean: tmp/sheaf/n8/closure/EtaFLevelRssAlignmentActual.lean.
- Compile: lake env lean -j1 -R D:/lean -> EXIT=0; one named sorry.

## Actual part

- carrier_eq : QCompletion X = K X := rfl, where QCompletion is
  Completion(nativeFPlaceOverBad) and K X is CommonPrimeCompletion F
  nativeFPlaceAtPrime.  Same actual F carrier, no bridge needed.
- qOClassFLevel := qOClass X mu, actual multiradial qO class.
- qOClassFLevel_eq = rfl.

## Exact gap

The two quotient types were elaborated with independently declared
MeasurableSpace/BorelSpace instances for the two type synonyms, so
FLevelRss and EtaRssAdmissibleCorrection.Rss are not definitionally the same
quotient type.  FLevelGlobalClassBridgeTarget records the exact missing
instance-compatible equivalence:
  Nonempty (FLevelRss X mu ≃ EtaRssAdmissibleCorrection.Rss X muK).
It is the named sorry.  Until supplied, qOClass cannot be defined directly in
GlobalRssAtF, and openClassF/closedClassF cannot be identified with
globalOpenClassAtF/globalClosedClassAtF by rfl.  No arbitrary quotient map is
chosen.