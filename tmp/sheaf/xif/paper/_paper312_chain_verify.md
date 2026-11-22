# Paper 3.12 concrete chain verification

Date: 2026-11-06 22:39 +08 (Asia/Shanghai), workspace D:/lean.

Command per file (serial, dependency order):

    lake env lean -j1 -R D:/lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/<Module>.olean tmp/sheaf/xif/paper/<Module>.lean

## Result: 8/8 EXIT=0, oleans present and newer than sources

| module | src bytes | SRC SHA256 | olean bytes | OLEAN SHA256 |
|---|---|---|---|---|
| PaperSignedHullNormalizationActual | 5817 | 0048416CEB948390757BA4269A726A3EF2626BAD79A4FF580744D1C117064954 | 78776 | C5E62FDAD8D00624D34C7D750596F3CEB3632BE2DBAC99EB514195D73A661F40 |
| C3GaussianThetaPacketActual | 5526 | 54902AEDCE6D636B2A6D4ED49E172B402BD186F89C58CDC5785778737CED4A9C | 61608 | 6BC802BA3717781C787F612B921D2CA7B5C6143C4D84DE1F1BB4A5BE63311FA6 |
| ConcreteHnormalActual | 4485 | 47234E08A36C1A85230D51CCDA56A8B01623A10489727540E3546C4D415EC483 | 56960 | 4382D8F55445267207AB5F900F343B6A784CEC09EBC9738818B042717379EAEA |
| NormalizedHaarHnormalActual | 5747 | D48D72512B50F7EC876D83853A2271C2B402B6B85037E18D3E9E54AD453C7321 | 112848 | F3C6D21BB62371F91E67B7796416BB5B92749CCD6BFAAA3697D7F9EEB4E659E2 |
| ConcretePaperSignedHullActual | 5297 | F206E52C7AFD47DEDF90F0C9BC276A48AA5C6CAD64978E3AF91533EED974EC0B | 56672 | B93D1B619449A072F970A6EB1F6891CA025233168E189EBB92F4A8821010662B |
| ConcreteSignedHullUnconditionalActual | 5264 | 4550B254AC629044FB4FC8B6F5B52649CF2A7EEDCEF72F077BBB240BDCDF0FC5 | 60768 | 82F2AED0D61EA3482EE11BCD890E09B36F5D23DDD56D152327F80D028E306F09 |
| ConcretePaperUnconditionalDataActual | 6151 | FADB5211595EA6D2FA8A44D6F4EC7B80B27BD3A5E4CE81C8B776B3751E7A6EC1 | 63128 | BA961671BA3EEFADAF46193F76AB39DF3D4C566E0B956EC81DC5EF81C9B7AFD1 |
| ConcretePaperUnconditionalDataUnconditionalActual | 5409 | ADB02FC96F6543C296C31343032CB5FBE7D21A5CE83F0FDBB93412D9430AB28A | 62888 | 30DD37FAD0AA9B403C9387DB549E44A039457130A84BB446F1AA8EA4A552F002 |

All oleans are newer than their sources. No sorry/axiom/True/PUnit/admit/native_decide
in code (comment-stripped scan of all 8 files).

## Axioms

`_paper312_axioms.lean` imports all 8 modules and runs `#print axioms` on 31
declarations (all main objects/theorems of the 8 files). Probe EXIT=0.
Every declaration: `[propext, Classical.choice, Quot.sound]` -- exactly the
allowed trio, no sorryAx/ofReduceBool/trustCompiler/custom axiom.

Probe files:
- _paper312_axioms.lean SHA256 EC120988F3BED3814F5D98C812FB6A11546AF129D944F42B2116B8A38135C9AA
- _paper312_axioms.out  SHA256 EA45DF67BBF3E9AD362F665582F332E0B28BF7D2712B60C7A5DD4684C25A1CA5

## Source fixes in this session

- PaperSignedHullNormalizationActual: added `import tmp.sheaf.n8.closure.C3Actual`,
  `open LeanFormal.IUT.N8Closure.C3Actual` (fixes "Invalid argument name l" at
  SourcePilotRegionDonors), and corrected 7 `SignedUnitFactorThetaIdentity`
  applications to take the donor D (not `actualSignedC3 D`, a SourcePilotRegionData).
- C3GaussianThetaPacketActual: added NumberFieldFinitePlace/C3Actual opens, removed
  nonexistent `open LeanFormal.IUT.IUTII.Theta`, set `K : Type ua`, `W : iota -> Type ui`.
- ConcreteHnormalActual: added NumberFieldFinitePlace/C3Actual opens, removed
  nonexistent PaperSignedHullSignedActual/HaarUnitFactorProof opens, aligned K/W universes.
- NormalizedHaarHnormalActual: added NumberFieldFinitePlace/C3Actual and
  PaperThetaMagnitudeSignedActual opens, removed nonexistent UnitReferenceMeasureActual
  open, aligned K/W universes, fixed `Measure.IsAddHaarMeasure.smul (μ := nu) ...`,
  unfolded `actualGaussianSignedAverage` before `ring`.
- ConcretePaperSignedHullActual / ConcreteSignedHullUnconditionalActual /
  ConcretePaperUnconditionalDataActual / ConcretePaperUnconditionalDataUnconditionalActual:
  source fixes (opens/universes/imports) landed concurrently from another worker;
  I recompiled each final source and verified EXIT=0.

## Note

Concurrent editing by another worker was observed (mtimes 22:11:46, 22:20:27,
22:17:59, 22:27:31); final compile results above are for the SHAs listed.
