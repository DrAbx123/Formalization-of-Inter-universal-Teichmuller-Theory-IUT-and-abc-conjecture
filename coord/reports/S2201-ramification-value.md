# S2201: ramification value status

Date: 2026-11-02. Layer O; consumer S2197/S2187/S2176.

## Actual

Lean:

  tmp/sheaf/xif/paper/S2201RamificationValueActual.lean
  SHA256 17F41A2D254BADBBCEEEC976CF137B19A16862FA281D5FFB64F81A9C09F19318
  EXIT=0
  olean SHA256 9A75ABEC706E1D03458EF0A5FB9F794627B0CF42CB53E93824D7C909DEC74951
  size 29336
  axioms propext, Classical.choice, Quot.sound.

Theorems:

- s2201_relativeCompletionDegree_eq_mul:
    relativeCompletionDegree = e * f (definitional);
- s2201_relativeRamification_dvd_completionDegree:
    e divides relativeCompletionDegree;
- s2201_unramified_iff_completionDegree_eq_residue:
    unramified ↔ e*f = f.

Exact missing aliases:

- s2201RamificationValueOne:
    global ramificationIdx = 1;
- s2201CompletionDegreeEq: e*f = f;
- s2201QVFamRamificationData;
- s2201CompletionCarrierBridgeMissing unchanged.

## First missing

Source data do not determine the qVFamTensorPlace ramification index.  The
actual value is

  (qVFamTensorPlace T b).maximalIdeal.asIdeal.ramificationIdx
    (RingOfIntegers Q).

No theorem computes it, and no source condition forces e=1 or e>1.  The
needed arithmetic input is exactly

  relativeCompletionDegree = relativeResidueDegree

or equivalently e=1.  Without it, hcNorm and the root coefficient norm remain
conditional.

## Conclusion

- BUILT: e*f identity, divisibility, unramified ↔ e*f=f.
- MISSING: actual e value / completion-degree equality; carrier bridge.
- no fake; no target-carrier change.
