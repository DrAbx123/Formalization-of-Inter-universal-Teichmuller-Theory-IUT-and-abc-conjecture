# etaAnab at the native F-place

- Task: ETA carrier correction.
- Owner: logdescent.
- Lean: tmp/sheaf/n8/closure/EtaAnabAtFPlace.lean.
- Compile: lake env lean -j1 -R D:/lean -> EXIT=0; one named sorry (Kummer vertical).

## Carrier correction

`NativeC3.nativeFPlaceOverBad X` is the actual F-completion place.  The file
uses `sourceLocalLogShellDatum (K := F)` at `nativeFPlaceAtPrime`, NOT
`C2Native.nativeLocalShell` (Fmod base shell).  No Fmod/F mixing.

## Actual data

- `localShellAtF := sourceLocalLogShellDatum (K:=F) (p:=FPlacePrime) nativeFPlaceAtPrime`;
- `integralStructureAtF := localShellAtF.logShell`;
- `volumeConsumerAtF := logShellVolumeConsumer (K := CommonPrimeCompletion F place)`;
- `EtaRssAtFPlace`: actual F log-shell subset, volume index, real log-volume
  coordinate; `etaRssAtFPlace` constructs it zero-sorry;
- `RssAtF := EtaRssAtFPlace X` (not bare Real);
- `IndAtFPlace` enum (Ind1 integral, Ind2 Kummer vertical, Ind3 upper-semi);
- `ind3UpperSemiAtF` uses production
  `VerticalLogKummerCorrespondence.HullDominates`.

## Exact gap

`kummerVerticalAtFActual := Nonempty VerticalLogKummerCorrespondence` has a
named sorry: production has only the conditional vertical contract, no
concrete Kummer vertical construction.

No direct Q/hull comparison; no Fmod shell.