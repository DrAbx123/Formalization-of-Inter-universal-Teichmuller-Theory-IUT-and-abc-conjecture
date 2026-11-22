# F-level Rss instance alignment: exact no-go

- Task: construct actual FLevelRss ≃ Rss by Quotient.congr / setoid equality /
  instance unification.
- Owner: logdescent.
- Lean: tmp/sheaf/n8/closure/EtaFLevelRssInstanceAlignment.lean.
- Compile: lake env lean -j1 -R D:/lean -> EXIT=0; one named sorry.

## What is actual

- carrier_eq : QCompletion X = K X := rfl (same carrier type);
- qOClassFLevel := qOClass X mu, actual multiradial F-level qO class.

## Why Quotient.congr does not instantiate

QCompletion uses the adicCompletion normed-field/metric/uniform structure;
K X uses commonPrimeCompletionNormedField.  Although the carrier types are
equal, the NormedField/UniformSpace/TopologicalSpace/BorelSpace instances are
not definitionally equal, and the two measures are separately typed.  Hence
PositiveFiniteRegion (QCompletion) and AdmissibleRegion (K) are not connected
by defeq, and Quotient.congr cannot be applied without an actual
instance-compatible region equivalence.

## Exact target

FLevelGlobalClassBridgeTarget : Prop :=
  Nonempty (FLevelRss X mu ≃ EtaRssAdmissibleCorrection.Rss X muK)
is the named sorry.  It is the exact required instance-compatible quotient
equivalence; until supplied, qOClass cannot be defined in GlobalRssAtF and
openClassF/closedClassF cannot be identified with global classes.  No arbitrary
quotient map was chosen.