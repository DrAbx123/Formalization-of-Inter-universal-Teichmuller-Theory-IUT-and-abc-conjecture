# Pushed Haar normalization at O_Q: exact no-go

- Task: close pushed(O_Q)=1 via preimage O_Q=O_K + Measure.map.
- Owner: logdescent.
- Lean: tmp/sheaf/n8/closure/EtaPushedNormalizedAtOQActual.lean.
- Compile: lake env lean -j1 -R D:/lean -> EXIT=0; two named sorries.

## Available actual

- qoContinuousAddEquiv : K ≃ₜ+ QCompletion (record actual, previous file).
- pushed := Measure.map qoContinuousAddEquiv muK; pushed_isHaar actual.
- O_Q_set_eq actual set equality of integral balls.

## Exact gaps

- PreimageOQEqualsOK: (qoContinuousAddEquiv)⁻¹'(O_Q)=O_K.  Proof requires a
  norm-instance bridge between commonPrimeCompletion (normalized completion
  norm) and the NormalizedCompletion norm used by
  normalizedCompletion_norm_le_one_iff.  Direct rewrite fails with instance
  mismatch, so the preimage membership theorem is missing.
- PushedNormalizedAtOQClosed: pushed(O_Q)=1, named sorry.  Follows once the
  preimage theorem is available (Measure.map + muK(O_K)=1).

No arbitrary normalization/transport.