/-!
# Manufactured p-adic norm tools: PARKED (Lead directive 2026-11-10 03:10)

Status: PARKED, not citable.  The requested p-adic norm tools ALREADY EXIST in
the repository, so manufacturing a replacement is unnecessary:

* LeanFormal.IUT.norm_ratCast_eq_padicNorm (LeanFormal/IUT/ABCBridge/Geometry/
  FreyTateAnalyticInput.lean:128): Mathlib's norm on Q_[p] restricts to
  padicNorm on the image of Q;
* LeanFormal.IUT.NumberFieldFinitePlace.norm_completionMap_pow_of_finrank_eq_
  relativeCompletionDegree (LeanFormal/IUT/ABCBridge/Geometry/
  RelativeCompletionFinrankReduction.lean:282) and
  norm_algebraMap_pow_of_finrank_eq_relativeCompletionDegree (:293): the
  unconditional canonical completion norm transport at the actual local degree;
* Example36.concretePlace_lower_absNorm / concretePlace_norm_completionMap_eq
  (LeanFormal/IUT/IUTII/Frobenioid/Example36SourceLogKummerIdentification.lean:
  277, 297): the concrete place absNorm = 5 and the actual isometry;
* BaseScalarValuationRelation.lowerPrimeValuation (LeanFormal/IUT/Foundations/
  AlgebraicGeometry/BaseScalarValuationRelation.lean:53): valuation of the
  rational scalar p in the lower completion.

These are recorded in coord/TOOL-INVENTORY.md (entry 2026-11-10 03:10) and are
used directly by S3133M2aClosedActual for the M2a closure.  No declarations,
no sorry, no axiom are provided by this parked module.
-/
