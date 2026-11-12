# S2187: qVFamily place unramified reduction

Date: 2026-11-02. Layer O; consumer S2176/S2040QVPlaceSplit.

## Actual

Lean:

  tmp/sheaf/xif/paper/S2187QVPlaceUnramifiedActual.lean
  SHA256 CCE77647C937686D0E337BE201B4DB82233505AA3B37062E416BBA430F922C7C
  EXIT=0
  olean SHA256 AE7DFC81F2215D1E076E4F8509D9E4030A97DD907E7FF82AEE1985213E797DB1
  size 23784
  axioms propext, Classical.choice, Quot.sound.

Theorem:

  s2187_unramified_iff_relativeRamificationIndex_one:
    S2040QVPlaceUnramifiedRequired T b
      ↔ relativeRamificationIndex (k := Q) (qVFamTensorPlace T b) = 1,

using localRamificationIndex_eq_relativeRamificationIndex.

Exact missing aliases:

- s2187QVFamUnramifiedRequired = S2040QVPlaceUnramifiedRequired;
- s2187QVFamGlobalRamificationOne = relativeRamificationIndex = 1;
- s2187CompletionFinrankOne = S2135CompletionFinrankOne;
- s2187CompletionCarrierBridgeMissing = S2176 bridge gap.

## Exact first missing

The actual arithmetic value of

  relativeRamificationIndex (k := Q) (qVFamTensorPlace T b).

No tree theorem computes it.  S2040QVPlaceSplitActual records the unramified
condition as missing; BadPlaceRationalDegreeActual deliberately does not fake
rational degree one.  The global finite-place ramification index is not
evaluated for qVFamTensorPlace.

Equivalently missing is the completion-degree equality
relativeCompletionDegree = qVFamTensorRationalDegree (e=1), but that equality
is not in the tree either.

## Carrier bridge

Unchanged: rootNormedAmbient -> CommonPrimeCompletion is not constructed;
S342 does not exclude a same-norm generator, so the bridge is undecided.

## Conclusion

- BUILT: unramified ↔ relative ramification index one.
- MISSING: actual computation of relativeRamificationIndex / completion
  degree equality; carrier bridge.
- no fake; no target-carrier change.
