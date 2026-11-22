# S2713 — Paper 3.12 final target and acceptance audit (audit only, no Lean)

Date: 2026-11-06. Owner: volumedet. Status: audit/interface record, NOT a proof,
NOT paper 3.12 closure.

## 0. Decision context

`S2711` was allowed to introduce a NEW `PaperUnconditionalDataMulti` and new
fields. The old `PaperXiFInclusion` / `PaperUnconditionalData` / concrete paper
chain remain frozen and must not be edited for this work. The new consumer is
written by logdescent.

## 1. Frozen old chain (reference, unchanged)

`PaperUnconditionalData` (PaperXiFUnconditional.lean:107) has:

```lean
sourceLink : PaperXiFSourceLink O P C3
sourceLink_holds : sourceLink.link_identification
thetaLink : PaperThetaLinkData ...
```

`PaperXiFSourceLink` (PaperXiFInclusion.lean:83) has:

```lean
source_identifications :
  O.paper_strip_identification /\
  O.paper_lineBundle_identification /\
  O.paper_logKummer_identification /\
  O.paper_qPilot_log_identification
qPilotLogVolume_eq_paper : O.qPilotLogVolume = paperQPilotLogVolume C3
link_identification : Prop
link_implies_inclusion :
  link_identification -> O.qPilotLogVolume in hullLogVolumeRay P.signedHullLogVolume
```

Consequences (old fields):

- `qPilot_mem_ray : O.qPilotLogVolume in hullLogVolumeRay P.signedHullLogVolume`
- `qPilot_le_signedHull : O.qPilotLogVolume <= P.signedHullLogVolume`

These are the targets the Multi version must reproduce, with the multi-q
normalization replacing `qPilotLogVolume_eq_paper` only by an explicit new
field. The old SHA chain (S2702/S2707 and the frozen concrete files) is not to
be changed.

## 2. Required fields of `PaperUnconditionalDataMulti`

The Multi structure must be a genuine data-carrying structure, not `True`/
`PUnit`/an empty placeholder. Minimum fields:

```lean
structure PaperUnconditionalDataMulti ... where
  sourceLinkMulti : PaperXiFSourceLinkMulti O P C3
  sourceLink_holds : sourceLinkMulti.link_identification
  thetaLink : PaperThetaLinkData ...
```

`PaperXiFSourceLinkMulti` must contain:

1. the actual four source identifications (same conjunction as the old
   `source_identifications`; no weakening);
2. `qPilotLogVolume_eq_paper_multi`: the multi-q normalization equality, an
   explicit proposition tying `O.qPilotLogVolume` to the multi-q paper scalar
   (e.g. a `WithTop Real`/weighted normalization, depending on the multi-q donor);
3. `link_identification : Prop` and
   `link_implies_inclusion : link_identification -> O.qPilotLogVolume in
   hullLogVolumeRay P.signedHullLogVolume`;
4. optionally the multi-q donor data itself as an explicit field, but it must
   not be an axiom or an unfilled `Nonempty` placeholder.

No field may be `True`, `PUnit`, a bare `Nonempty` without construction, or a
`sorry`-filled obligation.

## 3. Target theorems to be derived by the new consumer

From an inhabitant `D : PaperUnconditionalDataMulti`, the new consumer must
prove exactly:

```lean
D.qPilot_mem_ray :
  O.qPilotLogVolume in hullLogVolumeRay P.signedHullLogVolume

D.qPilot_le_signedHull :
  O.qPilotLogVolume <= P.signedHullLogVolume
```

These are real membership/order statements in the paper carrier, not `True` or
a definitional rewrite to the same proposition.

## 4. Axioms / kernel acceptance gate

Accepted only if ALL of the following hold:

1. source compiles with `lake env lean` EXIT=0;
2. olean exists and is fresh (mtime newer than source);
3. `#print axioms` of the consumer and of every exported theorem gives exactly
   `[propext, Classical.choice, Quot.sound]`;
4. no `sorryAx`, no new `axiom`, no `native_decide`, no `True`/`PUnit` gate;
5. SHAs (source and olean) recorded;
6. imports do not pull a module whose olean carries `sorryAx`.

Any deviation fails the gate. Axioms cannot be "accepted because the theorem is
conditional": conditional hypotheses are fine, but the proof term must still be
kernel-clean.

## 5. Conditions under which paper 3.12 must NOT be claimed closed

Paper 3.12 / the IUT IV estimate / ABC must not be claimed closed if any of:

1. `hq` is still an explicit property with no actual inhabitant; in particular
   for the concrete two-place S1280 data `concreteQLogIdentification` is
   uninhabited (single C3 q vs two-place source bad-q structure mismatch).
2. `hcomp` / the multi-q donor is still an explicit input, not actual.
3. the two IUT IV comparison gaps remain named fields:
   `height_le_normalizedRegionVolume` and
   `regionVolume_le_normalizedWeight`;
4. the paper carrier is only the named `IQHullLogVolumeInterface`, not the
   literal paper inductive system;
5. the `(1,0)` q-pilot object/arithmetic line bundle/log-Kummer comparison is
   not constructed;
6. any theorem in the dependency cone has `sorryAx` or an extra axiom;
7. the old frozen S2707 remains conditional on `hq` (its documented status).

In all these cases the honest statement is:

> Multi consumer is actual/conditional on the listed explicit inputs; paper 3.12
> is not closed. The remaining work is the multi-q donor plus the two IUT IV
> comparison gaps and the literal carrier.

## 6. Freeze / recompilation rule

- Old chain stays frozen: no edits to `PaperXiFInclusion.lean`,
  `PaperXiFUnconditional.lean`, `ConcretePaperUnconditionalDataActual.lean`,
  `ConcretePaperUnconditionalDataUnconditionalActual.lean`,
  `S2702PaperConditionalActual.lean`, `S2707PaperUnconditionalActual.lean`.
- New Multi consumer is a NEW file; it may import old modules read-only.
- If any old dependency is edited, the entire old chain must be recompiled in
  order and its SHAs re-recorded before claiming the new consumer is verified.

## 7. Verdict

This audit defines the exact target and gate for `PaperUnconditionalDataMulti`.
It does not construct the Multi data, does not prove paper 3.12, and does not
alter the frozen concrete chain. Current status: audit only; new consumer
pending logdescent (multi-q donor actual required before any closure claim).
