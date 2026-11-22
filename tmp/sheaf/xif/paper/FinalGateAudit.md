# Final gate / axiom audit: PaperLevelXiFTargetActual vs ProofActual

## 1. Compilation

* `PaperLevelXiFTargetActual.lean`: local `lake env lean` EXIT=0.
* `PaperLevelXiFTargetProofActual.lean`: local `lake env lean` EXIT=0.
* `FinalGateAuditActual.lean`: local `lake env lean` EXIT=0.

The proof file required one compilation fix: its `set_option maxHeartbeats
1000000open MeasureTheory` line was malformed and heartbeats stayed at
200000; the option and `open` are now on separate lines. The actual proof
term was not changed.

## 2. Target type

`PaperLevelXiFTargetActual.ActualPaperXiFTarget`:

    {l} (T : SourceNativeInitialThetaData l)
    [Fintype (Bad (nativePlaceSelection T))]
    [∀ b, MeasurableSpace (qVFamTensorBlock T b)]
    [∀ b, BorelSpace (qVFamTensorBlock T b)] : Prop

It is `actualQPilotSignedLogClassical T ≤ actualThetaHullLogRoot T`, where:

* q scalar = weighted `c_norm * log p` with supply c_norm;
* theta scalar = weighted normalized log of the actual root theta closure
  hull with root coefficient `c_norm/(2l)`.

## 3. Transport proof conclusion

`PaperLevelXiFTargetProofActual.globalQPilotLog_le_globalThetaHullLog`:

    {l} (T : SourceNativeInitialThetaData l)
    [Fintype (Bad (nativePlaceSelection T))] :
      PaperLevelXiFTargetProofActual.globalQPilotLog T ≤
        PaperLevelXiFTargetProofActual.globalThetaHullLog T

This is a real scalar inequality between the proof-local scalars:

* `globalQPilotLog = ∑ b, nativeBadLocalWeight b * perBQPilotLog b`;
* `globalThetaHullLog = ∑ b, nativeBadLocalWeight b * perBThetaHullLog b`;
* `perBQPilotLog` uses `qPilotClassicalLog` at `rootNormCoefficient`;
* `perBThetaHullLog` uses `rootThetaHullLog` at
  `rootHalfCoefficient = rootNormCoefficient/(2l)`.

`paperLevelXiFTargetData` packages the same proof-local scalars and the
global inequality.

## 4. Consistency verdict

The proof conclusion is **not literally the target proposition**.
There is currently no theorem of the form

    actualQPilotSignedLogClassical T ≤ actualThetaHullLogRoot T,

and no bridge theorem identifying the proof-local scalars with the target
scalars. The proof proves a mathematically analogous scalar inequality on its
own normalized root-hull model; the target uses its own `actualQPilotSignedLogClassical`
and `actualThetaHullLogRoot` definitions.

Consequently:

* `statement_compiles`: yes for target;
* `proof_body_checked`: yes for proof-local inequality;
* `kernel_closed`: yes for proof-local inequality;
* `target_accepted`: **no** — the target proposition is not yet derived.

## 5. Exact bridge obligations for final acceptance

A final bridge must prove (or provide as actual definitions/equalities):

1. the q-scalar identification
   `-globalQPilotLog T = actualQPilotSignedLogClassical T`
   (weighted normalized `c_norm * log p` equality);
2. the theta-scalar identification
   `globalThetaHullLog T = actualThetaHullLogRoot T`
   (equality of the two root closure hull logs, including the `c_norm/(2l)`
   coefficient and the canonical unit normalization);
3. the implication from 1, 2 and
   `globalQPilotLog ≤ globalThetaHullLog` to `ActualPaperXiFTarget`.

Only after these bridge theorems are proved can the target be accepted.

## 6. Axiom audit

`#print axioms` on the transport proof:

* `perBQPilotLog_le_perBThetaHullLog`: [propext, Classical.choice, Quot.sound]
* `globalQPilotLog_le_globalThetaHullLog`: [propext, Classical.choice, Quot.sound]
* `paperLevelXiFTargetData`: [propext, Classical.choice, Quot.sound]

No `sorryAx`, no extra axiom. The target itself has no proof yet, so it has
no axiom audit as a closed theorem.

## 7. Final status

The proof file compiles and is axiom-clean for its own statement, but the
paper target `ActualPaperXiFTarget` is not yet closed. Final gate must remain
open until the two scalar bridge equalities are proved.
