# Eta Gaussian special-value volume: exact no-go

- Task: BPS volume-diff formula.
- Owner: logdescent.
- Lean: tmp/sheaf/n8/closure/EtaGaussianSpecialValueVolume.lean.
- Compile: lake env lean -j1 -R D:/lean -> EXIT=0; one named sorry.

## Actual part constructed

- actualA := C3.qUnit (completion unit a);
- actualGaussianPower n j := thetaCompletionActual C3 n j = a^(gaussExponent j),
  actual, with rfl equality.

## Exact no-go

The BPS formula volume(A S)-volume(S) = log|Norm(g)|/d_j with
g = zeta*a^(j^2) requires:
1. an actual completion root-unit zeta and the source theta special value in
   the completion;
2. the actual tensor-block normalized volume/determinant identity.

Production gives only a^(j^2) (`thetaCompletionActual`), with no actual lift of
the source root unit/theta value to the completion.  The exact missing source
theta value is `ThetaPacketIdentification` (source real theta scale = finite
theta packet scale), registered as the named sorry
`missingActualThetaValue_obligation`.  The tensor-block volume formula is also
absent.  No arbitrary g or volume surrogate is introduced.