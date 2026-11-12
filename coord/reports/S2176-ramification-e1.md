# S2176: qVFamily unramified/e=1 and carrier bridge audit

Date: 2026-11-02. Layer O; consumer S2170/S2157/S2154.

## Actual

Lean:

  tmp/sheaf/xif/paper/S2176RamificationE1Actual.lean
  SHA256 96514B769EA8919A58F71442CF0F62C75EF16337C4CA3BF802B97BA78B312ABD
  EXIT=0
  olean SHA256 9701A1E4DC5CD0EBC507E67762AF21F23ED27E3CC708091180EB40E71388777B
  size 71456
  axioms propext, Classical.choice, Quot.sound.

Definitions/theorems:

- s2176QVFamUnramified :
    localRamificationIndex (k := Q) (qVFamTensorPlace T b) = 1;
- s2176_hcNorm_iff_unramified:
    (qVFamNormalizedCoefficient = order)
      ↔ s2176QVFamUnramified,
  under QVFamNormalizedNormCompatibility at the actual local ramification
  index;
- s2176_rootGenerator_norm_of_unramified:
    under that compatibility and unramified, the S2157 root generator has
    norm p^(-(qVFamPaperRootCoefficient));
- s2176QVFamUnramifiedRequired = S2040QVPlaceUnramifiedRequired;
- s2176CompletionCarrierBridgeMissing:
    Nonempty (s2157RootCarrier -> CommonPrimeCompletion).

## Exact first missing

1. Actual unramified computation:
     localRamificationIndex (k := Q) (qVFamTensorPlace T b) = 1.
   This is exactly S2040QVPlaceUnramifiedRequired, recorded as a missing
   split/descent condition; the tree does not compute the qVFamily place
   ramification index.  Note BadPlaceRationalDegreeActual deliberately does
   not fake rational degree one.

2. Carrier bridge:
     s2176CompletionCarrierBridgeMissing.
   The root-ambient generator is not a CommonPrimeCompletion generator.
   S342 excludes the completion 2l-th root of q, but not a same-norm
   generator; the bridge is undecided, not refuted.

## Verdict

e=1 is an actual source condition, not a consequence of the tree.  If it is
supplied, the root generator norm is correct in the root ambient.  To use it
for ArithmeticTuplePureFractionalScalingData one must either supply the
CommonPrimeCompletion bridge or change the target carrier.  No target change
is made here.

## Conclusion

- BUILT: hcNorm iff unramified at the actual local ramification index; root
  generator norm under unramified.
- MISSING: unramified/e=1 computation; carrier bridge or target-carrier
  modification.
- no fake; no S2040 assumption.
