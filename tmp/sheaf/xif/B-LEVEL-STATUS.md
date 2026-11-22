# Xi-f B-level status (value-layer carrier)

Date: 2026-10-28. Scope: value-layer/conditional surrogate. **Not paper-level xi-f; no target_accepted.**
Task-498 update: B-level exact obstructions formalized in `XiFBLevelObstruction.lean`.

## Unified compile evidence

```text
tmp/sheaf/xif/SourceXiFConstruction.lean  EXIT 0
tmp/sheaf/xif/XiFQPilot.lean              EXIT 0
tmp/sheaf/xif/XiFHullVolume.lean          EXIT 0
tmp/sheaf/xif/XiFScaling.lean             EXIT 0
tmp/sheaf/xif/XiFContraction.lean         EXIT 0
tmp/sheaf/xif/XiFComparisonData.lean      EXIT 0
tmp/sheaf/xif/XiFCertificate.lean         EXIT 0
tmp/sheaf/xif/XiFBLevelObstruction.lean   EXIT 0
```

Compile command: `lake env lean -j1 -R D:/lean ...` (serialized through `lean-serial`).
The B-level file has no `sorry`, no `axiom`, and no toy/arbitrary carrier.

## B-level result: not reachable on the current value-layer carrier

### 1. `hq : q <= 1` is an independent/source-bridge condition

`XiFContraction.lean` proves the exact positive bridge:

```lean
SourceQContractionBridge : Prop :=
  exists b : I.initial.badPlaces,
    (I.theaterAt 0 0).thetaPacket.q = I.initial.reduction.qParameter b
```

- `q_le_one_of_sourceQContractionBridge`: the bridge implies `q <= 1`.
- `q_lt_one_of_sourceQContractionBridge`: it implies `q < 1`.
- `q_le_one_iff_imageLogDegree_nonpos`: `q <= 1` iff every theta-pilot image has nonpositive source local log-degree.
- If `1 < q`, the actual hull/image inequality fails (`not_hullVolume_le_imageVolume_of_one_lt_q`).

`OriginalInput` contains no declaration linking the initial reduction `qParameter` to the theater `thetaPacket.q`, and no theorem gives `q <= 1` unconditionally. The bridge is a named source condition, not an internal consequence.

### 2. `hScaling` is false under pointwise degree faithfulness

`XiFScaling.lean` names the exact scaling condition `ValueLayerScalingCondition` and proves:

- `not_valueLayerScalingCondition_of_degreeFaithful`: under pointwise degree faithfulness `hdeg`, the scaling condition is false.
- `valueLayerScalingCondition_counterexample_of_degreeFaithful`: explicit counterexample; the constant theta-pilot point of exponent 1 lies in `sourceScalingUnits` and has positive log-degree `card(SourceVolumeIndex l)`.
- `valueLayerScalingCondition_iff_hullVolume_le_imageVolume_of_q_le_one`: under `q <= 1`, the scaling condition is exactly the remaining half of the R9 hull/image inequality.

Therefore `hScaling` cannot be proved from `OriginalInput` or from `q <= 1`; under the actual degree-faithful regime it is **false**. It remains the ambient O-module/`1,circ U` compactness input, not a value-layer theorem.

### 3. The value-layer surrogate cannot imply paper xi-f

`XiFBLevelObstruction.lean` proves the exact scalar mismatch, using the actual `sourceQPilotLogVolume_eq_gauss`:

```lean
sourceQPilotLogVolume = card(SourceVolumeIndex l) * log q.
```

The paper q-pilot signed scalar is `-log q`. The file proves:

- `sourceQPilotLogVolume_ne_paperSignedLogScalar`: for `log q != 0`, the raw value-layer q-pilot scalar is not `-log q`.
- `normalizedQPilotLogVolume_ne_paperSignedLogScalar`: dividing by the cardinality gives `log q`, still not `-log q`; a separate sign/root normalization would be required.
- `bLevelExactObstructions`: conjunction of the bridge implication, the false-scaling theorem, the counterexample, and the scalar mismatch.

Object-level mismatches (task-491 audit, unchanged):

| paper object/statement | value-layer surrogate |
|---|---|
| q-pilot object at `(1,0)` | theta-pilot point at signed label `j=1` |
| `-|log q|` | `card * log q` raw / `log q` normalized |
| procession-normalized signed `1,circ U` hull volume `-|log Theta|` | `sSup` of pointwise source log-degrees over the value-monoid hull |
| xi-f membership `-|log q| in R_{<= -|log Theta|}` | pointwise hull-sup inequality under `hq`/`hScaling` |
| determinant / `O(-)` / normalized log-volume comparison | absent |
| Ind1/Ind2/Ind3 | not represented in the value-layer file |

## Consequence

```text
B-level as 'remove hq and hScaling from the value-layer surrogate' is refuted/blocked:
  q <= 1        : independent source condition (missing SourceQContractionBridge)
  hScaling      : false under pointwise degree faithfulness
```

The value-layer xi-f is a conditional surrogate only. It cannot be substituted for paper xi-f, cannot supply `target_accepted`, and does not construct the paper q-pilot/hull objects.

## What remains for paper-level xi-f

1. Actual q-pilot object at `(1,0)`, arithmetic line bundle and log-Kummer representation.
2. Actual signed `1,circ U` holomorphic hull with compactness, procession average, and Haar/log-shell normalization `-|log Theta|`.
3. O-module/arithmetic vector bundle/localization layer (SHE landing).
4. Paper xi-f membership in `R_{<= -|log Theta|}` from the link identification.
5. Signed certificate / `Cor312Conclusion` consumption with actual IPL/SHE/APT evidence.

These are separate source-object constructions, not consequences of the value-layer surrogate.

target_accepted=false. No fake theorem, no axiom, no mixed/E3.
