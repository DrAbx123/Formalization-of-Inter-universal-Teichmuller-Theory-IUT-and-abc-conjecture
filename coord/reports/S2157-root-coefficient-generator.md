# S2157: actual root coefficient generator in the root-stack ambient

Date: 2026-11-02. Layer O; consumer S2154/S2144/S2139.

## Actual

Lean:

  tmp/sheaf/xif/paper/S2157RootCoefficientActual.lean
  SHA256 67628184DC11194AA1F58AB8B9C8342181897D2499BE7BD4316B0E0057755A98
  EXIT=0
  olean SHA256 6E4DF13267B367A00EC16D981174E9269024254A0703FFB5AF3C3CA55B37F12C
  size 69472
  axioms propext, Classical.choice, Quot.sound.

Definitions:

- s2157RootCarrier := rootNormedAmbient T b (the normed ambient of the
  actual root-stack extension L = K(root));
- s2157RootCoefficientGenerator := rootNormedElement T b (the actual
  2l-th root);
- s2157RootCoefficientGenerator_norm, conditional on
    QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b
      = order(qVFamily T b):
    ||root|| = p^(-(qVFamPaperRootCoefficient T b)),
  i.e. exactly the paper root coefficient exponent, not p^(-order).

## Exact first missing

1. hcNorm:
     QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b
       = order(qVFamily T b).
   The log-norm coefficient is order/e for ramification index e; equality
   requires e = 1.  This is exactly the normalization condition recorded in
   QVFamNormalizedCoefficientOrderAuditActual.
2. Carrier bridge: the generator lives in rootNormedAmbient, while
   ArithmeticTuplePureFractionalScalingData requires a generator in
   CommonPrimeCompletion.  No tree map identifies rootNormedAmbient with the
   completion (S342 rules out the completion root of q).  This is
   s2157CompletionCarrierBridgeMissing.

Thus the actual root-extension generator has the required norm under e=1,
but cannot yet instantiate the CommonPrimeCompletion scaling data.

## Consequence for S2144/S2139

Given hcNorm and a carrier bridge to CommonPrimeCompletion, the root
coefficient supply would be actual and S2144 would close root minimal region
compact/closed.  Neither is assumed here.

## Conclusion

- BUILT: actual root coefficient generator in the root-stack ambient and its
  norm identity conditional on e=1.
- MISSING: e=1 normalization hcNorm, and root-ambient-to-CommonPrimeCompletion
  carrier bridge.
- no fake; no S2040 assumption.
