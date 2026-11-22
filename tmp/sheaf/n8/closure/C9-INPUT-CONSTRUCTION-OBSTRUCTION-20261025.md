# OriginalInput -> Input construction: exact obstruction

Date: 2026-10-25. Status: OPEN. No Lean proof attempted beyond inspection.

## What exists

1. SourceTheorem311Realization.input
   File: SourceHodgeTheaterBridge.lean lines 928-952.
   Builds Theorem311Source.Input from a realization R.
   It consumes R.procession/R.packet/R.vertical/R.evaluation/R.genericFamily.

2. SourceTheorem311Completion.realization
   File: SourceRealizationLifting.lean line 1213.
   Builds SourceTheorem311Realization from completion C.
   But C has a field `input : Input` at line 47.
   So the completion package already contains the Input it is supposed to build.

3. SourceInternalWiring/SourceP1P2Input
   File: SourceInternalWiring.lean lines 380 and 1393.
   Structures with fields LGPBoundary/VolumeBoundary/KummerBoundary/
   PermutationBoundary; no constructor from OriginalInput.

## Exact obstruction

No declaration in the audited Theorem311 tree has type
  OriginalInput l V -> Theorem311Source.Input Label Choice
or
  OriginalInput l V -> SourceP1P2Input ...

The only Input constructor consumes a realization; the only realization
constructor consumes a completion that already contains Input. This is a
definitional cycle at the source-boundary layer, not a provable bridge.

Audit.sourceTheorem311Realization status is interface; its own note says
'existence for arbitrary arithmetic data is not claimed'.

## Consequence

To construct OriginalInput -> Input one must add the actual IUT I-II
source data: LGP/volume/Kummer/permutation boundaries, H1H2Alignment,
H2SpokePermutation, K2FrobenioidBoundary, SourceP1P2Bundle, and the
completion q/scale/horizontal fields. None is derived from OriginalInput
in the current corpus.

Instantiating arbitrary structures would be a toy input, not a proof.

Status: no Lean construction; target_accepted=false.
## Raw-data inspection from OriginalInput

OriginalInput fields: initial : SourceDefinition31Data; family :
SourceHodgeTheaterFamily; index_equiv; arithmetic_alignment.

The family gives HodgeTheater records with arithmetic, primeStrip, thetaPacket
(q and scale), plus links/permutation. It does NOT give:

- DPrimeStripProcession ind1/ind2/ind3/base/level actions;
- ProcessionPacketProfile possibleImage/logVolume/determinant;
- LocalTensorPacket;
- VerticalSiteData nonarchimedean/archimedean images;
- EvaluationSystem;
- LabelledKummerIso;
- HorizontalLGPLink;
- SourceHodgeTheaterSystem.link as a carrier self-map (HodgeTheaterLink has
  only primeStripEquiv + q/scale equalities, not a HodgeTheater endomap).

Therefore no raw construction OriginalInput -> SourceTheorem311Realization ->
Input is present. Supplying these fields would be a new source-boundary
extension, not a construction from OriginalInput.

## First raw construction attempt: SourceHodgeTheaterSystem

Attempted Lean file: tmp/sheaf/n8/closure/C9HodgeSystemFromOriginal.lean.

From OriginalInput.family one can project:

- source := I.initial;
- index := I.family.index;
- theater := I.family.theater;
- distinct, permutation, qParameter, scale, q/scale naturality.

But SourceHodgeTheaterSystem.link requires an endomap
  theaterCarrier -> theaterCarrier
for every pair of indices. HodgeTheaterLink contains only
  primeStripEquiv + theta_q_eq + theta_scale_eq,
not a HodgeTheater endomap. Therefore the family link cannot define
SourceHodgeTheaterSystem.link without adding a new carrier map.

Using identity link would satisfy refl/trans but discard the prime-strip
transport, so it is not source-faithful. The attempt was stopped rather than
installing a toy link.

Conclusion: the first raw object (SourceHodgeTheaterSystem) is already blocked
at the carrier-link map; constructing Input from OriginalInput requires defining
that map and the missing SourceLGPProcession/packet/vertical/evaluation data.
