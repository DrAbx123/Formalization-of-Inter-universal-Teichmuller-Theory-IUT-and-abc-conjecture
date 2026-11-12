# S2170: e=1 normalization and root-carrier bridge audit

Date: 2026-11-02. Layer O; consumer S2157/S2154/S2144.

## Actual

Lean:

  tmp/sheaf/xif/paper/S2170RootCarrierBridgeActual.lean
  SHA256 E104BA2BE763D3334315857ED75282B1C3DC0BD3D21CD936E48A4A2DFC569B47
  EXIT=0
  olean SHA256 8E8285BD19770FDD5DA1FA31F853C249EEEC5443F2DC5FDF3E020C63E2096208
  size 27712
  axioms propext, Classical.choice, Quot.sound.

Contents:

- s2170_hcNorm_iff_e_eq_one (e) (hepos) (hcomp):
    (qVFamNormalizedCoefficient = order) ↔ e = 1,
  under QVFamNormalizedNormCompatibility with ramification index e.
- s2170_rootGenerator_norm_of_e_eq_one:
    under e = 1 and that compatibility, the actual root generator has
    norm p^(-(qVFamPaperRootCoefficient)), not p^(-order).

## Exact first missing

1. QVFamNormalizedNormCompatibility with the actual relative ramification
   index e, plus e = 1.  The tree proves the iff and the order/e formula, but
   does not compute e for the qVFamily place.  This is the hcNorm gap.
2. CommonPrimeCompletion generator:
     s2170CompletionRootGeneratorMissing :
       Nonempty (s2154GeneratorAt (qVFamPaperRootCoefficient)).
   The S2157 actual generator lives in rootNormedAmbient; no map
   rootNormedAmbient -> CommonPrimeCompletion exists in the tree.
   s2170RootAmbientToCompletionBridgeMissing records this exact carrier gap.

## Verdict on unreachable

The root coefficient norm is realized on the root-stack ambient under e=1.
On CommonPrimeCompletion it is still undecided: S342 does not exclude a
same-norm generator, and the norm value-group discreteness theorem is absent.
Changing the target carrier to the root-stack extension would make S2157's
generator usable but requires changing ArithmeticTuplePureFractionalScalingData
away from CommonPrimeCompletion.

## Conclusion

- BUILT: e=1 iff hcNorm, and root generator norm under e=1.
- MISSING: actual e=1/ramification computation; root-ambient to completion
  carrier bridge (or target-carrier change).
- no fake; no S2040 assumption.
