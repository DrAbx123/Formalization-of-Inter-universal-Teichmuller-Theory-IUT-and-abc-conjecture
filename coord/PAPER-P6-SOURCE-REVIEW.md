# Paper P6 full target: source semantics self-review

Date: 2026-10-25. Reviewer: Lead (self-review, not independent).
Scope: target only; no new Lean edits.

## Elaborated target

```lean
def PaperP6FullTarget :
  {l : PrimeGeFive} → SourceInitialThetaData l → Prop :=
fun S =>
  PaperP6Target S ∧ PaperValuesBoundedTarget S
```

where

```lean
PaperP6Target S :=
  exists qLog thetaLog : Real,
    qLog = log ||qUnit S|| /\
    thetaLog = thetaLogVolume S /\
    qLog <= thetaLog /\
    (thetaLog : WithTop Real) < top

PaperValuesBoundedTarget S :=
  forall T : Set (Block S),
    T subset c6Hull ->
    log ((c6UnitRefNormalizedData T).toReal) <= thetaLogVolume S
```

## Input object

`SourceInitialThetaData` is the IUT I Definition 3.1 source contract with clauses A-F, selected after the audit in PAPER-INITIAL-DATA-AUDIT.md as substantially more paper-faithful than SourceDefinition31Data.

Actual fields used:
- candidate.arithmetic: actual number fields Fmod/F/K and curve;
- clauseB.bad_nonempty: actual nonempty bad set;
- clauseB.qParameter at the chosen bad F-place: actual `FinitePlaceQCandidate`;
- clauseA/D structure via actual orbicurve/unit objects when forming the one-factor C6 block.

Not used as assumptions in the proof: opaque coherence Props and clause fields not needed for Q/Theta; they remain part of the qualified input contract, not target fields.

## Q

`p0` is chosen from `clauseB.bad_nonempty`; `pF` is an actual lift to F; `qCandidate = clauseB.qParameter pF pF_bad`; `qAtPrime = q = qCandidate.q`. `qUnit = Units.mk0 qAtPrime`.

`QPaperNorm_actual` proves log(normalized q-pilot region mass)/d = log||qUnit||. Hence `qLog = log||qUnit||` is the actual q readout, not an arbitrary Real.

## Theta

`thetaLogVolume` is log of the C6 unit-reference-normalized mass of `c6Hull`, where `c6Hull = arithmeticTupleCanonicalHull` (actual C6 hull), and the normalization uses `arithmeticTupleCanonicalUnitReference` with mass one.

`thetaLogVolume_lt_top` proves finiteness from the actual raw canonical-region measure and finite scalar normalization.

## ValuesBounded

`PaperValuesBoundedTarget` states the paper bound for every region contained in the C6 Theta hull. This is a universal actual theorem (not a chosen finite Real set): `paperValueLog_le_theta_of_subset` proves it by actual measure monotonicity and log monotonicity.

Remaining source bridge: the actual paper Values family (ellOut images of source objects) and its provenance inclusion in `c6Hull` are not constructed here; C9Paper.ValuesPaper/QPaper/ThetaPaper provenance bridge remains the C9BridgeGap already recorded.

## Verdict

Self-review verdict: the target is source-qualified, non-circular, and does not assume its conclusion. `S : SourceInitialThetaData` is an allowed qualified input per GOAL.md; the proof uses actual Q/Theta objects and proves Q<=Theta, Theta finite, and hull ValuesBounded.

Not claimed: final paper 3.11/3.12 full conclusion (Theta^pm, actual Values provenance, C9 output, ABC transition). Not claimed: independent review or comparator acceptance.

Status: source semantics self-review valid for the candidate target; target_accepted=false pending independent review/comparator.
