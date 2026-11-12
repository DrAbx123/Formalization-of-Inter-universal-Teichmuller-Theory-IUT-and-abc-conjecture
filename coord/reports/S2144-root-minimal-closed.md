# S2144: rootMinimalRegion compact/closed from scaling data

Date: 2026-11-02. Layer O; consumer S2139/S2137 root hull gap.

## Actual

Lean file:

  tmp/sheaf/xif/paper/S2144RootMinimalClosedActual.lean
  SHA256 2B00AB9CF41BF5F8DA61B431C087261068A76CD55E94210AC51A55F3DBFB33EA
  EXIT=0
  olean SHA256 B595ADD63C0BA4DD503DC30D9231ED2C44F68EA4A832739E48001E6AACA05950
  size 64432
  axioms propext, Classical.choice, Quot.sound.

Theorems:

  s2144_isCompact_rootMinimalRegion_of_data
    (data : ArithmeticTuplePureFractionalScalingData places tuple c) :
    IsCompact (thetaTensorScaledRegion c)

  s2144_isClosed_rootMinimalRegion_of_data
    (data : ...) : IsClosed (thetaTensorScaledRegion c).

Proof uses the actual identity
arithmeticTupleFractionalLattice_mul_holomorphic_eq_pureGenerator_smul:
the scaled region is the multiplicative translate of the compact open
canonical unit reference by the pure tensor of the scaling data's local
generators, hence compact and closed.

## Consequence

RootMinimalRegionClosedGap is now reduced to the scaling data:

  ArithmeticTuplePureFractionalScalingData
    (qVFamTensorPlaces T b) qVFamTensorTuple
    (rootThetaCoefficient T b oneSignedLabel).

No separate closedness theorem is needed once that data exists.

## Exact first missing

The scaling data for the paper root coefficient.  Existing actual
qVFamPureFractionalScalingData is for the order coefficient, and
QVFamPureFractionalScalingDataGapActual records the exact
NormalizedGeneratorSupplyMissing (default completion norm vs normalized
CommonPrimeCompletion norm).  There is no root-coefficient generator/norm
supply in the tree.

Also still open from S2139: zero-label correction for rootThetaImageSet
(all SignedLabel vs NonzeroLabel), Haar positivity/finiteness of the root
hull, and the hull equality with the minimal region.

## Conclusion

- BUILT: conditional compactness and closedness of thetaTensorScaledRegion
  from actual scaling data.
- RootMinimalRegionClosedGap no longer independent: given scaling data it is
  closed.
- MISSING: root coefficient ArithmeticTuplePureFractionalScalingData
  (NormalizedGeneratorSupplyMissing), plus zero-label/Haar/hull equality.
- no fake; no S2040 completion assumed.
