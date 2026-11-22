# Preimage O_Q and actual pushed normalization: closed

- Task: close PreimageOQEqualsOK and PushedNormalizedAtOQ.
- Owner: logdescent.
- Lean: tmp/sheaf/n8/closure/EtaPreimageOQActual.lean.
- Compile: lake env lean -j1 -R D:/lean -> EXIT=0; zero sorry.

## Actual proof

- norm_commonPrime_eq_normalized: rfl, identifies the commonPrimeCompletion
  norm with the normalizedCompletion norm (norm-instance bridge).
- O_Q_eq_closedBall: O_Q = closedBall 0 1.
- preimage_O_Q: (qoContinuousAddEquiv)⁻¹'(O_Q) = O_K.  Proof uses the actual
  value equality homeomorph_apply_eq_ringEquiv, the norm bridge, and
  normalizedCompletion_norm_le_one_iff.
- pushed_O_Q: applied Measure.map, O_Q measurability via O_Q_eq_closedBall,
  preimage_O_Q and actual muK(O_K)=1.
- PushedNormalizedAtOQ_closed: closes the previous target.

No arbitrary normalization/transport; zero sorry.