# S1229: SourceProcessionBoundary audit

Read: `LeanFormal/IUT/IUTIII/Theorem311/SourceProcessionBoundary.lean`,
S1221StripOfChoiceActual, S1225SourceChoiceCoreActual,
ParametricCarrier/MultiradialOutputKernel/MultiradialProfileKernel.

## Does SourceProcessionBoundary provide actual Core/Profile?

No.

`SourceProcessionBoundary.Input` is a **consumer boundary**, not a constructor:

```text
structure Input where
  theater : HodgeTheater
  history : HodgeTheaterHistory theater
  carrier : Carrier Label Choice        -- taken as a field
  baseChoice : Choice
  baseChoice_eq : ...
  packetVolume : Choice -> Real
  packetVolume_eq_profile : ...
  base_packetVolume_eq_theta : ...
  target_q : Real
  ...
```

It assumes an already-constructed `Carrier Label Choice` and only proves
relations among its profile/base packet volume/theater theta log-volume.  It
does not construct `Core`, `Profile`, or a carrier on `I.family.index`.

`concreteInput` uses the **concrete finite model**
`ConcreteFiniteTheorem311.ProcessionChoice`, not an arbitrary
`I.family.index`.  It is not a source-index connection for arbitrary
`OriginalInput`.

There is no `source_index` map from `I.family.index` to the boundary's
`Choice`; the boundary is generic in `Choice` only as a parameter.

## Minimal actual path

1. Already actual:
   - S1221 `stripOfChoice : I.family.index -> FPrimeStrip V`
   - S1221 `linkOfChoice i j : FPrimeStripEquiv (stripOfChoice i) (stripOfChoice j)`
   - S1225 horizontal/vertical/translate permutations and
     `sourceInd1/sourceInd2/sourceInd3`
   - S1225 `sourceLogVolume c := (I.family.theater c).thetaPacket.logVolume`
2. Next actual (permutation identities, no source gap):
   - prove the 15 `Core` laws for `sourceInd1/2/3`, level (constant 0 or an
     actual level if available);
   - build `Core Label (I.family.index)`.
3. Then `Profile` needs the exact field
   `S1225LogVolumeShiftLaws`:
   ```text
   sourceLogVolume (sourceInd1 g c) = sourceLogVolume c
   sourceLogVolume (sourceInd2 g c) = sourceLogVolume c
   sourceLogVolume c <= sourceLogVolume (sourceInd3 n c)
   ```
   This is not supplied by SourceProcessionBoundary; its link facts only
   concern the fixed `theater`/`history.terminal` pair, not arbitrary family
   index shifts.
4. Only after Core+Profile can a `Carrier` be assembled; then
   `AlgorithmInput` and `SourceRun` on `Choice = I.family.index`.

## Exact first field

For arbitrary `I : OriginalInput l V`, the first exact field is still

```text
S1225LogVolumeShiftLaws
```

(equivalently, the `Profile.ind1_invariant/ind2_invariant/ind3_upper` fields).
SourceProcessionBoundary does not remove it; it is downstream of a carrier.

The Core laws themselves are not a source gap (they are permutation/zpow
identities), but they are not yet proved in the tree.

## Consumer

The assembled carrier is needed before the planned
`SourceOutputPrimeStripInterpretation` SourceRun and before the
`iplAlgorithmicProvenanceCard` consumer.  No wrapper is written here.
