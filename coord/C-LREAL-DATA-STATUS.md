# C-LREAL-DATA-STATUS — concrete L record and R obstruction (A984)

Status: concrete L record EXISTS, but **R : ∀v, SourceImageRealization v** is not
constructible from it (value-monoid action obstruction).  GAP recorded.

## 1. Concrete L record / input path (green, olean TRUE)

`S1487OQPilotScalarEqualityActual.lean`:
- `S1487W := FinitePrimePlace 2 7` (:177);
- `S1487FivePlace : FinitePlaceAtPrime GaussianField 5` (:128);
- `S1487Strip n m : FPrimeStrip S1487W` (:186):
  `Pi/G := Multiplicative (Int × Int)`, `Mon := SourceHaarActualValueMonoid`,
  `action := sourceHaarActualTrivialAction`, `degree := sourceHaarActualDegree`;
- `S1487OriginalInput S : OriginalInput l S1487W` (:379);
- `S1487FaithfulInput := S1487OriginalInput S1487FaithfulSourceData` (:537);
- `S1487FaithfulC3 : SourcePilotRegionDataL (I := S1487FaithfulInput)` (:548),
  built by `actualSourcePilotRegionDataL ... S1487FivePlace`; olean true.

So `actualSourcePilotRegionDataL` **can** be instantiated for this concrete I/place;
the earlier carrier mismatch is resolved for V = FinitePrimePlace 2 7.
`SourceProcessionBoundary.Input.concreteInput l` supplies the boundary
(value `concreteInput l`, olean true).

## 2. ValueMonoidAt / SourceImageRealization data

- `ValueMonoidAt 0 0 v := (I.primeStripAt 0 0).Mon v`
  (`SourceImageHull.lean:82`);
- for the S1487 input this is `SourceHaarActualValueMonoid`
  `= Multiplicative sourceHaarActualNonpositiveAddSubmonoid`
  (`SourceUnitRegionHaarDataActual.lean:52`);
- its degree `sourceHaarActualDegree` has **nonpositive** real part (:57-66);
- the only positive-real action is
  `sourceHaarActualPositiveRealAction : Multiplicative Real →* SourceHaarActualValueMonoid`
  and it is **constantly 1** (:76-82): a group can map to the nonpositive-degree
  value monoid only trivially.

`SourceImageRealization v` (`SourceImageHull.lean:161`) requires
`posRealAction (ofAdd (log q))` with degree exactly `log q`.  For the S1487 strip:
- any `posRealAction` from the group `Multiplicative Real` to a monoid of
  nonpositive degrees is trivial (image subgroup of the monoid of values ≤ 1 is
  `{1}`); hence its degree is 0;
- `log q ≠ 0` for the concrete q (`S1487Cand` has norm 1/5, log ≠ 0);
- therefore no `SourceImageRealization` exists on this model value monoid.

## 3. Minimal data needed for R

Instead of `SourceHaarActualValueMonoid`, need for each v:
1. a value monoid `Mon v` with a genuine group action of `Multiplicative Real`
   (not trivial), and
2. a degree hom `Mon v →* Multiplicative Real` such that
   `degree (action (ofAdd (log q))) = log q`;
equivalently, a section of the degree map at the element realizing `log q`.

The concrete L record's `S1487Strip` uses the toy nonpositive monoid
(`sourceHaarActual...`) and cannot supply this; the actual p-adic/adelic value
monoid with its positive-real action is the missing source object.

## 4. Consequences

- The S1487 concrete L record is green and can feed C1/C2/C3L fields, but it
  does NOT compute R; S3137's `R : ∀v, SourceImageRealization v` remains missing.
- No `Mzk1SourceImageRealizationLActual.lean` written (would require a fake
  action or a different value-monoid model).
- Next: either construct the actual value monoid/action (source obligation), or
  use a model value monoid with a nontrivial positive-real action (then R is
  model-computable but not the actual paper R).
