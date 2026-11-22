# S2733 — evidence audit: signedHullLogVolume vs paper -|log Theta|; globalThetaHull vs paper theta hull

Date: 2026-11-07. Evidence-based, NOT name-based. No closure claim.

## 1. Is `signedHullLogVolume` the paper `-|log(Theta)|`?

NO equality theorem exists; it is NOT the paper theta-hull log-volume.

### Definition and constraints

```lean
PaperSignedHull.signedHullLogVolume (P) :=
  -((P.ambient.logVolume P.ambient.hull).toReal)   -- PaperSignedHull.lean:80
```

`PaperSignedHull.ambient : IQHullLogVolumeInterface X`.  The interface only
requires:

- `imageSet ⊆ hull`;
- `hull ⊆ scaleShift '' unitRegion`;
- `logVolume` monotone, unitRegion finite, scaling monotone;
- `hull_logVolume_eq_average : ambient.logVolume ambient.hull = ofReal procession.average`.

There is NO field/theorem saying `ambient.imageSet` is the paper union of
possible images of a Theta-pilot object, nor that `ambient.hull` is the paper
holomorphic hull under (Ind1)-(Ind3).  Hence the structure admits different
`ambient`/`procession` choices with different signed values; no equality with
the paper object is derivable.  `S2711P` is the concrete Gaussian signed hull,
not the paper theta image hull.

### Actual source theta image/hull (contrast)

`S2725ThetaImageHullActual` (actual):

```lean
I.possibleThetaPilotImageSet v R n ⊆ I.sourceHolomorphicHull v R n
I.sourceHolomorphicHull v R n is the least candidate hull
```

`signedHullLogVolume` does not reference `I.sourceHolomorphicHull` or
`I.possibleThetaPilotImageSet`.

Verdict: EQUALITY UNPROVEN; structural counterexample by underdetermination.

## 2. Is `globalThetaHull = unitRegion` the paper theta image/hull?

NO.  The equality is a unit-region substitution, not the paper hull.

### Proved equalities

```lean
globalThetaHull          = globalThetaImageSet       -- globalThetaHull_eq_imageSet
globalThetaImageSet      = actualC3LogShellTensorRegion
globalThetaUnitRegion    = actualC3LogShellTensorRegion
```

So `globalThetaHull = unitRegion` holds by construction: the "hull" is the
C3 log-shell tensor region, which is also the unit region.

### Paper source comparison

IUT III Corollary 3.12, lines 566-570: `-|log(Theta)|` is the
procession-normalized mono-analytic log-volume of

> the holomorphic hull of the union of the possible images of a Theta-pilot
> object, relative to the relevant Kummer isomorphisms, in the multiradial
> representation subject to (Ind1), (Ind2), (Ind3).

It is NOT the C3 log-shell tensor unit region.  The actual source image/hull
objects are:

```lean
I.possibleThetaPilotImageSet v R n  : Set (I.ThetaPilotPoint v)
I.sourceHolomorphicHull v R n       : Submonoid (I.ThetaPilotPoint v)
```

on a DIFFERENT carrier from
`GlobalThetaCarrier C3 = C3LogShellTensorBlock C3`.

Consequently `globalThetaHull = unitRegion` is the unit-region substitution
(FAIL as the paper theta hull), not an actual identification with the paper
hull.  No theorem equates `globalThetaHull` with `I.sourceHolomorphicHull`.

Verdict: FAIL / INSUFFICIENT as paper theta hull.

## 3. Consequences for S2717

- q side: uses actual `paperQAbsLog fiveLabel logQ` (S2691), no exp(-theta)
  circularity; q side is evidence-clean.
- theta side: S2717 now uses the actual S2725 C3 global hull log-volume, but
  that hull is the unit-region substitution above; it is NOT the paper theta
  hull of possible images.
- Therefore S2717 remains CONDITIONAL and must not be reported as paper 3.12
  closure.  The theta-side object is the true remaining problem.

## 4. S2738 / S2739 support gate

- S2738 `J` must satisfy `support J = arithmeticPrimeSupport (abcRationalPoint a c)`;
  if not equal, FAIL.
- S2739 `J` must satisfy the same equality; if not, FAIL.
- Equality (not merely superset) is required by the gate; no bad-only support
  substitution is acceptable.

## 5. S2739 support evidence via S2741

S2739 gate:

```text
support J = arithmeticPrimeSupport (abcRationalPoint a c)
```

Evidence from `S2741RadicalProductActual`:

```lean
S2741_prod_support_eq_radical_abc (h : IsABCTriple a b c) :
  (prod p in arithmeticPrimeSupport (abcRationalPoint a c), p)
    = natRadical (a * b * c)
```

and `RationalPrimeSupport.arithmeticPrimeSupport_abcRationalPoint`:

```lean
arithmeticPrimeSupport (abcRationalPoint a c) = (a * b * c).primeFactors
```

So a finite support S certified by the S2741 radical-product equality
(with prime elements) is the ABC support; the gate must use this equality,
not a superset/subset approximation.

Verdict: S2739 support evidence = S2741 radical-product equality; if support J
is not equal, FAIL.

## 6. S2749 support gate

S2749 support must be an EQUALITY:

```text
support S2749 = arithmeticPrimeSupport (abcRationalPoint a c)
```

not superset/subset/bad-only. Evidence as in section 5 (S2741).
