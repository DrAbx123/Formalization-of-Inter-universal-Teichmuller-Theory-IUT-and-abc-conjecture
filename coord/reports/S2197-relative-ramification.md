# S2197: relative ramification/completion degree reduction

Date: 2026-11-02. Layer O; consumer S2187/S2176.

## Actual

Lean:

  tmp/sheaf/xif/paper/S2197RelativeRamificationActual.lean
  SHA256 BBF4B451D3D2B8DACF6CCCB08AA680FAE61F9F26E94B2E0B5BD5555AF6E04722
  EXIT=0
  olean SHA256 DDEFF1D58E61E1C421E6DC21CAFB059EC30622F2C7C6BED9046C7AD22D9B5B7D
  size 37928
  axioms propext, Classical.choice, Quot.sound.

Theorems:

- s2197_relativeRamification_eq_global:
    relativeRamificationIndex (k := Q) (qVFamTensorPlace T b)
      = (qVFamTensorPlace T b).maximalIdeal.asIdeal.ramificationIdx
          (RingOfIntegers Q);
- s2197_unramified_iff_completionDegree_eq_residue:
    S2040QVPlaceUnramifiedRequired T b
      ↔ relativeCompletionDegree = relativeResidueDegree.

Exact missing aliases:

- s2197RelativeRamificationValue = e = 1;
- s2197CompletionDegreeEq = e*f = f;
- s2197GlobalRamificationIdx = global ramificationIdx = 1;
- s2197CompletionCarrierBridgeMissing unchanged.

## Exact first missing

The actual numerical value of

  (qVFamTensorPlace T b).maximalIdeal.asIdeal.ramificationIdx
    (RingOfIntegers Q)

is absent.  This is the global finite-place ramification index e of the
qVFamily F-place over its rational prime.  No theorem evaluates it; the tree
only records S2040QVPlaceUnramifiedRequired as a missing split condition and
BadPlaceRationalDegreeActual refuses to fake rational degree one.

Equivalently missing: relativeCompletionDegree = relativeResidueDegree.

## Conclusion

- BUILT: relative ramification = global ramificationIdx; unramified iff
  completion degree equals residue degree.
- MISSING: actual value/computation; carrier bridge.
- no fake; no target-carrier change.
