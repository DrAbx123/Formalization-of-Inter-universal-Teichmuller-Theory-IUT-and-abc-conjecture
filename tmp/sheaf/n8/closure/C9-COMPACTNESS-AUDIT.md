# C9 production/compactness audit (2026-10-23)

## Available compactness datum

`SourceOneCircUCompactness (v R n)` in `OModuleCompactnessLayer.lean` provides:
- `oneCircU : Set (ThetaPilotPoint v)`
- `image_subset_oneCircU`
- `layer : SourceOModuleLayer v` with log-degree bound
- `scaling : ThetaPilotPoint v`
- `hull_subset_scaledRegionImage`

This is a **named premise**, not a construction from `OriginalInput`.

## What it implies

`sourceOModuleCompactness_haarData` fills `SourceUnitRegionHaarData` and gives
finiteness/positivity data for the hull log-volume. It does NOT by itself give:
- `QSigned <= ThetaSigned`
- `sourceHullVolume <= imageVolume`

The C9 target `QSigned<=ThetaSigned` is equivalent to the hull/image comparison
(xi-d), while compactness only bounds hull volume by a scaled O-region.

## Current status

- `sourceScalingUnits_nonpos` is refuted under degree faithfulness
  (`not_sourceScalingUnits_logDegree_nonpos_of_degreeFaithful`).
- Therefore C9 finite-phase cannot be obtained from the current value hull/scaling.
- Need either the actual paper `1,circ U` hull definition with source compactness, or a
  corrected Q/Theta identification from the paper.

No N8 closure claimed; no fake assertion.