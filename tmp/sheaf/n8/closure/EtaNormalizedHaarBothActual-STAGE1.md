# Actual normalized Haar measures at both F carriers

- Task: construct normalized Haar measures instead of assuming normalization.
- Owner: logdescent.
- Lean: tmp/sheaf/n8/closure/EtaNormalizedHaarBothActual.lean.
- Compile: lake env lean -j1 -R D:/lean -> EXIT=0; one named sorry (transport).

## Actual construction and normalization

- O_K := Integers (K X), massK := addHaar(O_K),
  muK := (massK)^-1 • addHaar on K; muK(O_K)=1 proved.
- O_Q := Integers (QCompletion X), massQ := addHaar(O_Q),
  muQ := (massQ)^-1 • addHaar on QCompletion; muQ(O_Q)=1 proved.
- massK_pos_lt_top / massQ_pos_lt_top: actual positivity and finiteness from
  the production theorem measure_localIntegers_pos_lt_top.
- normalized_haar_readout_agree: direct corollary of the previously proved
  normalized_haar_agree_on_everywherePos.

## Exact remaining gap

NormalizedHaarCarrierTransport: identifying the normalized Haar measure on
QCompletion with the normalized Haar measure on K along the carrier equality.
Recorded as a named sorry; no arbitrary transport is chosen.