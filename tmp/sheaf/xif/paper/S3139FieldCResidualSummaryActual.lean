/-!
# S3139: field (C) — final residual summary (component documentation)

This module records, per team policy §11, the exact remaining residual of the
first-triangle field (C) (the Real scalar channel of the @F_mod^x@ copies,
IUT III:616-620, Fig. I.5; Formalization of IUT (2026-04) :514-524) together
with its owner, the concrete construction plan against actual objects, why the
current actual inputs are insufficient, and the named consumers.

## Constructed (actual)

* @S3139FieldCArchimedeanLogActual.sourceFmodArchimedeanLog@: the actual
  additive archimedean norm-log of the units of the actual @F_mod@ (production
  @infinitePlaceLog@ at a supplied infinite place, via @algebraMap@ into the
  completion) — EXIT=0, axioms trio.
* @S3139FieldCArchimedeanLogActual.sourceFmodArchimedeanScalarCharacter@ and
  @sourceInfinitePlaceScalarCharacter@: the actual multiplicative Real scalar
  character of @F_mod^x@, i.e. the paper-faithful *realified* copy scalar
  channel, with the explicit archimedean choice datum
  @SourceInfinitePlaceChoice@.
* @S3139FieldCCopyActionActual.sourceInd2CopyActionDataOfScalarCharacter@ and
  @sourceArchimedeanCopyActionData@: the paper-faithful @SourceInd2CopyActionData@
  built from the actual archimedean character (copies act by independent
  per-factor scalar actions, preserving the splitting-monoid scalar action),
  after proving the tensor-level one/multiplicativity laws for the actual
  @ind2TensorEquiv@.
* @S3139FieldCConjugateActual.SourceConjugateLocalUnitMap.conjugateAut@,
  @conjugateValue@, @conjugateAut_mul_apply@: the actual local Frobenius action
  on the value-monoid fibers and its realified degree readout.

## Residual (exact missing data, owner + plan)

* C1 — the archimedean place choice for the realification.  Owner: stepxi.
  Exact datum: @SourceInfinitePlaceChoice@ (an infinite place of the actual
  @F_mod@).  Page refs: III:616-620, Fig. I.5.  Plan: source the choice from the
  actual infinite-place dictionaries (@SourceCompletion@/infinite-place
  completion, production archimedean local records) when the paper's chosen
  place is fixed; conversely any supplied choice already yields the actual
  scalar channel above.  Why not determined: @InitialThetaArithmeticData@ has no
  infinite-place field, so the choice is extra data.
* C2 — the finite-place conjugate map.  Owner: stepxi (co-owner shehdd/stage4
  for placeToMod/cusp real encoding).  Exact datum:
  @SourceConjugateLocalUnitMap@ (@F_mod^x@ -> local @Pi@ fibers, multiplicative).
  Page refs: III:616-620, Fig. I.5, Remark 3.11.1.  Plan: compose the global
  conjugate action (local reciprocity/local unit map) with the actual
  @FPrimeStrip.action@; why insufficient now: the tree has the local Frobenius
  actions (@FPrimeStrip.action@, @unitsAction@, @timesMuAction@) and local
  Galois actions, but no global @F_mod^x -> local units@ conjugate map.
* C3 — the tensor-factor identification of the finite-place channel.  Owner:
  stepxi.  Exact datum: an identification of the value-monoid fibers with the
  log-shell tensor factors (the same log-shell module realization as field
  (A)); plan: use the (A) capsule source data once it is realized; this is the
  precise sense in which the (Ind1) convention bridge depends on (A)
  (@S3139FieldCConjugateActual.SourceInd1BridgeDependency@).

## Consumers

First-triangle mutation (@SourceMultiradialRepresentation@); lattice/mainline
q/Theta comparison and R1/M-fields; @SourceInd2CopyActionData@ (task-27 shape).

## Negative result policy

The Real ring embedding @F_mod -> R@ used in task-27 is a modeling bridge only;
the paper-faithful construction is the realified scalar channel above.  The
observation that some actual fields admit no real embedding is a
model/convention mismatch and is recorded in the ledger as negative, never
promoted.
-/
