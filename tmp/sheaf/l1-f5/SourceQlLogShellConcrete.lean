import tmp.sheaf.xif.paper.S3132SourceQlLogShellConcreteActual

/-!
# Source `Q_l` log-shell concrete map — repair module

The construction formerly in this file now lives in the importable module
`tmp/sheaf/xif/paper/S3132SourceQlLogShellConcreteActual.lean`, which re-exports
the namespace `ABCBridge.SourceQlLogShellConcrete`.

Reasons for the move and the repair of the former EXIT=1:

* the former line-48 error `Unknown identifier isometry_localField_algebraMap`
  was a missing import: the actual lemma
  `LeanFormal.IUT.LocalFieldLogarithm.isometry_localField_algebraMap` is proved
  in `LeanFormal/IUT/Foundations/LocalFields/IntegralUnitGaloisDescent.lean`;
* the former line-58 kernel deterministic timeout came from a hand-written norm
  computation; the direct `unitLog`/`integralUnitMap` isometry route also
  triggered a slow normed-algebra instance search, so the repaired module uses
  instead the already-compiled actual `Q_5` field comparison
  (`concretePlace_qFiveComparisonRingEquiv`,
  `concretePlace_principalUnitsEquiv`) of
  `Example36SourceLogKummerIdentification` and the analytic `log1p` transport;
* the directory component `l1-f5` contains a hyphen and is not a valid Lean
  module component, so this file cannot be imported by consumers; the consumer
  `tmp/sheaf/xif/paper/S3129IQHullLogVolumeSourceActual.lean` carries its own
  compact source-image construction.

Source correspondence: IUT III, Definition 1.1 and Remark 1.2.2 (log-shell),
Proposition 1.2; IUT III, Example 3.6 (concrete local data).
-/

#check ABCBridge.SourceQlLogShellConcrete.sourceQlPrincipalUnitLogImage
#check ABCBridge.SourceQlLogShellConcrete.sourceQlPrincipalUnitLogImage_subset_principalUnitLogShell
#check ABCBridge.SourceQlLogShellConcrete.sourceQlLogShellImage
