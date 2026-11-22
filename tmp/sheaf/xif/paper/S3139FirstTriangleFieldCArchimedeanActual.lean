import LeanFormal.IUT.InfinitePlaceLogDictionary
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# S3139: field (C) — paper-faithful Real realification of F_mod^x from actual archimedean data

Field (C) of the first-triangle residual is the Real scalar through which the
copies of `F_mod^x` act on the tensor packets of log-shells (IUT III:616-620,
Fig. I.5; Formalization of IUT (2026-04) :514-524).  The task-27 formulation
used a ring embedding `F_mod -> Real` as a modeling bridge; this file replaces
it, where the actual arithmetic data allows, by the *actual archimedean
realification*:

* the actual archimedean local field at an infinite place is Mathlib's
  completion `v.Completion`, and the production archimedean log
  `infinitePlaceLog v : Additive (v.Completion)^x ->+ R` is the actual additive
  norm-log (kernel = norm-one units, surjective: `InfinitePlaceLogDictionary`);
* embedding the actual `F_mod` into its completion by `algebraMap` and taking
  units gives the actual additive log
  `sourceFmodArchimedeanLog A v : Additive (A.Fmod)^x ->+ R`, and exponentiating
  gives the actual multiplicative Real scalar character
  `sourceFmodArchimedeanScalarCharacter A v : (A.Fmod)^x ->* R^x`.

Two data choices are not determined by the actual input and are recorded as
exact missing data (owners + plans in the ledger):

* `SourceInfinitePlaceChoice`: which infinite place (hence which archimedean
  realification) is used.  `InitialThetaArithmeticData` has no infinite-place
  field, so the choice must be supplied; the tree's actual archimedean
  dictionaries apply to any supplied infinite place (III:616-620, Fig. I.5).
* `SourceConjugateLocalUnitMap`: the conjugate action of `F_mod^x` on local
  units at the *finite* places (Frobenioid `placeToMod` / cusp real encoding,
  owned by the shehdd/stage4 streams).  The tree has local-unit actions
  (`FPrimeStrip.unitsAction`, local Galois actions) but no global
  `F_mod^x -> local-units` map, so the finite-place channel cannot yet be
  constructed.

**Component, not paper object.**  Named future consumer: the copy-action data
`SourceInd2CopyActionData` (task-27) and the lattice/mainline q/Theta readouts.
No sorry/axiom/True/PUnit/toy carrier.
-/
