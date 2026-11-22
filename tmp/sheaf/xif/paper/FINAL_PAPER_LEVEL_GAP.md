# FINAL PAPER-LEVEL GAP: normalized hull theorem vs ThetaLink/PaperUnconditionalData

Scope: read-only audit of the actual Lean files. No Lean object is added and
no missing field is asserted.

## 1. What the final normalized theorem proves

`PaperXiFFinalActual.paperLevelXiF_actual` proves

    ActualPaperXiFTarget (l := l) T

for a `SourceNativeInitialThetaData T`, with local instances for Fintype Bad,
MeasurableSpace/BorelSpace on each `qVFamTensorBlock T b`. The target is

    weighted Σ c_norm * log p
      ≤ weighted Σ normalizedLog(rootThetaHull_b),

using the actual qVFamily normalized coefficient and the actual root theta
closure hull. It is a scalar tensor-lattice statement.

It does **not** construct or consume:

* a paper q-pilot object `PaperQPilotObject O`;
* a paper signed hull `PaperSignedHull P`;
* a `SourcePilotRegionData C3`;
* a `ThetaLinkActual O P C3`;
* a `PaperUnconditionalData v O P C3`;
* `IPLActual` / `KummerEvaluationActual` for paper strip vertices;
* actual paper Ind1/Ind2/Ind3 actions on the paper output carrier;
* actual SHE landing/APT output.

## 2. Exact fields of `ThetaLinkActual`

From `ThetaLinkActual.lean`, an instance requires:

| field | content | supplied by final theorem? |
|---|---|---|
| `qPilot_identifications` | four `O.paper_*_identification` fields | no O |
| `qPilotLogVolume_eq_paper` | `O.qPilotLogVolume = paperQPilotLogVolume C3` | no O, no C3 |
| `qParameter`, `qParameter_pos`, `qParameter_log_ne_zero` | actual paper q scalar | only normalized c_norm scalar; no O |
| `qPilotLogVolume_eq_neg_abs` | `O.qPilotLogVolume = -|log qParameter|` | no O/paper scalar |
| `link_identification` | actual paper Theta-link/q-pilot link Prop | no link object |
| `link_implies_inclusion` | link identification → membership in signed hull ray | no `PaperSignedHull` |

None of these is derivable from `ActualPaperXiFTarget`: the final theorem has
no `PaperQPilotObject`, no `PaperSignedHull`, no `C3`, and no link/Ind
structure. A scalar inequality cannot instantiate an object record with these
fields.

## 3. Exact fields of `PaperUnconditionalData`

From `PaperXiFUnconditional.lean`:

| field | content | supplied by final theorem? |
|---|---|---|
| `sourceLink : PaperXiFSourceLink O P C3` | four q-pilot identifications; `O.qPilotLogVolume = paperQPilotLogVolume C3`; `link_identification`; `link_implies_inclusion` | no |
| `sourceLink_holds` | proof of `sourceLink.link_identification` | no |
| `thetaLink : PaperThetaLinkData` | `ipl : IPLActual` with lower horizontal strips, Kummer arrow, evaluation arrow, input link, factorization; `kummerEvaluation : KummerEvaluationActual` with two-path equality | no |

`PaperThetaLinkData.ipl` specifically consumes the five paper strip vertices
`intermediateStrip gauStrip envStrip coricEnvStrip qPilotStrip`, the actual
`FPrimeStripEquiv` components, `SourceKummerArrow`, `SourceEvaluationArrow`, and
the frozen factorization. The final theorem has none of these paper strip
vertices; it operates on `qVFamTensorBlock T b` and `qVFamTensorPlaces`.

## 4. Can actual qVFamily/root hull instantiate `ThetaLinkActual`?

**No, not directly.** The actual qVFamily and root hull provide only a
normalized scalar/tensor-hull construction. `ThetaLinkActual` needs all of:

1. a `PaperQPilotObject O` with actual G/envStrip and four nonempty paper
   identifications;
2. a `PaperSignedHull P` with actual IQ/procession ambient data and the
   `hull_logVolume_eq_average` normalization identification;
3. a `SourcePilotRegionData C3` with its actual C3 q parameter;
4. the bridge `O.qPilotLogVolume = paperQPilotLogVolume C3`;
5. the bridge from the root tensor hull normalized log to
   `P.signedHullLogVolume` (or at least enough to prove the link implication);
6. the actual link identification and its implication.
Only items 1-3 could potentially be sourced from other actual files
(`PaperQPilotObjectConcreteActual`, `ConcreteSignedHullUnconditionalActual`),
and even then the scalar bridges 4-5 are different quantities: the final
normalized `c_norm` tensor scalar vs. `PaperQPilotObject.qPilotLogVolume`/
`paperQPilotLogVolume C3`, and the root tensor closure log vs. the IQ/procession
`PaperSignedHull.signedHullLogVolume`.

## 5. Missing actual fields by consumer

### `ThetaLinkActual`

* `O : PaperQPilotObject`;
* `P : PaperSignedHull`;
* `C3 : SourcePilotRegionData`;
* `qPilot_identifications` (four actual paper identifications);
* `qPilotLogVolume_eq_paper`;
* `qParameter` normalized to the paper q scalar;
* `qPilotLogVolume_eq_neg_abs`;
* `link_identification`;
* `link_implies_inclusion`.

### `PaperUnconditionalData`

All `ThetaLinkActual` fields plus:

* `PaperXiFSourceLink` fields;
* `PaperThetaLinkData.ipl : IPLActual` at actual paper strip vertices;
* `PaperThetaLinkData.kummerEvaluation : KummerEvaluationActual`;
* the actual `link_identification` proof.

### Paper Θ-link / Ind / multiradial layer

* actual F^⊩×μ / Θ×μ-LGP link data at the paper strip vertices;
* actual Ind1 (carrier/procession permutation) action on the paper output carrier;
* actual Ind2 (F_l^×/label permutation) action on the paper tensor packet;
* actual Ind3 upper-semi log-Kummer correspondence;
* the multiradial representation region and its holomorphic hull;
* the actual Kummer isomorphisms used to compare the two sides.

`IndeterminaciesActual.lean` supplies value-layer Ind1/Ind2 actions and a
value-layer Ind3 correspondence, not the paper log-shell/tensor-packet
realization. `IPLAPTActual.lean` supplies actual IPL/Kummer-evaluation
structures but requires paper strip vertices; it does not identify the final
tensor block with those strips.
## 6. What can be reused

The final normalized theorem is a valid **scalar tensor-hull** result and can
serve as the scalar core of a later paper-level assembly. Its reusable parts:

* actual weighted qVFamily normalized scalar;
* actual root theta closure hull with coefficient `c_norm/(2l)`;
* actual normalized log of that hull;
* weighted global inequality.

What must still be built for `PaperUnconditionalData`/`ThetaLinkActual`:

* paper q-pilot object with actual identifications;
* paper signed hull with actual IQ/procession normalization;
* scalar bridges normalized-tensor ↔ paper q/hull;
* paper strip vertices and actual IPL/Kummer-evaluation;
* actual Ind1/Ind2/Ind3 paper-level actions;
* actual link identification and link-implies-inclusion.

## 7. Verdict

The final normalized hull theorem is **not** an instance of `ThetaLinkActual`
or `PaperUnconditionalData`, and no such instance can be manufactured from
the actual qVFamily/root hull data alone. The exact missing fields are listed
above. The normalized theorem is a scalar core, not the paper-level
Theta-link/multiradial comparison.
