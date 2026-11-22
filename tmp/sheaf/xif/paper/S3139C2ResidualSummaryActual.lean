/-!
# S3139: C2 — residual summary and construction inventory (component documentation)

Per team policy §11, this module records the state of C2 (the finite-place
conjugate channel of the copy action: global @F_mod^x -> local units, IUT
III:616-620, Fig. I.5, Remark 3.11.1) with the constructed candidates, the
exact missing datum, its owner, construction plan, why current actual inputs are
insufficient, and the named consumers.

## Constructed from actual data (this batch)

* @S3139C2FiniteCompletionUnitsActual.sourceFmodUnitsToFiniteCompletion@:
  the natural candidate global-units-to-local-units map at every actual finite
  place of @F_mod@, through the actual completion embedding
  @algebraMap A.Fmod (NumberFieldFinitePlace.Completion W)@; a group
  homomorphism by construction (its multiplicativity and unit laws proved).
* @S3139C2InfiniteCompletionUnitsActual.sourceFmodUnitsToInfiniteCompletion@:
  the archimedean companion, and the identification
  @sourceFmodArchimedeanLog_eq_infinitePlaceLog@ showing the field-(C) actual
  archimedean Real realification IS the archimedean instance of this channel.

## Exact missing datum (owner + plan)

* C2 residual — @S3139C2LocalDegreeDataActual.SourceFmodLocalElementMap@: the
  multiplicative map @(F_mod)^x -> (F.Mon v)^x@ at every fiber of the prime
  strip (the placeToMod/cusp conjugate alignment).  Owner: stepxi, co-owner
  shehdd/stage4 for placeToMod/cusp/LGP local units.
  Page refs: III:616-620, Fig. I.5, Remark 3.11.1.
  Plan: identify the actual completion units (constructed above) with the
  prime-strip local units through the placeToMod map (the same identification as
  the cusp real encoding), then compose.  Why insufficient now: the tree has the
  *local* actions (@FPrimeStrip.action@, local Frobenius groups, degree) and the
  actual completions, but no global-to-local element/place alignment; the
  prime-strip is an abstract structure, not yet tied to @F_mod@'s completions.
* Once the element map is supplied, the realified degree channel is constructed
  and proven multiplicative: @localDegree@, @localDegree_mul@, @localDegree_one@,
  @localDegreeAdd@, @localDegreeAdd_mul@, @localScalarUnit@, @localScalarUnit_mul@
  (the only data the realified copy action consumes).

## Relation to the archimedean channel

The archimedean realification (field (C)) needs no placeToMod: it uses the
actual infinite-place completion directly.  C2 is its genuinely finite-place
analogue; the two channels are the two families of localizations of the same
global units.

## Consumers

Finite-place copy action (@SourceInd2CopyActionData@); first-triangle mutation;
lattice/mainline q/Theta comparison.  No sorry/axiom/True/PUnit/toy carrier.
-/
