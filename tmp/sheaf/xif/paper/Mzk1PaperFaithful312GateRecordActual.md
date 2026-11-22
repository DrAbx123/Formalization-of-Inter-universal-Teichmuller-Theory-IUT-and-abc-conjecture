# A732 gate record — paper-faithful 3.12 normalized hqneg route (shehdd)

All single-file `lake env lean -o` (watchdog off).

## Assembly chain
1. `Mzk1PaperFaithful312HqnegActual` (EXIT=0, olean=True)
   - `hqneg_iff_rpVolume_lt_one`: `requirementSignedQ (rpRequirement T) < 0 ↔ rpVolume T (rpRegion T) < 1`
   - `final_3_12_of_hqnegEvidence` (conditional evidence route)
2. `Mzk1PaperFaithful312RpNormalizationActual` (EXIT=0, olean=True)
   - direct `hqneg_direct` modulo the single Prop `RpUnitBallHaarOne T`
   - `rpVolume_rpRegion_lt_one`
3. `Mzk1PaperFaithful312NormedActual` (EXIT=0, olean=True)
   - normalized volume: `rpVolumeNorm T S = (haar T S).toReal / (haar T (fullRegion T)).toReal`
   - `rpRequirementNorm` (`strict_measure` = green raw strictness / positive denominator)
   - **`hqneg_norm` UNCONDITIONAL**
   - **`final_3_12_normed`** (only IPL/SHE/APT evidence parameters)
4. `Mzk1PaperFaithful312FinalActual` (EXIT=0, olean=True)
   - **`final_3_12_concrete`** and `final_3_12_concrete'` from the direct route

## Gate lines (verbatim `#print axioms`)

```
'...Mzk1PaperFaithful312NormedActual.hqneg_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'...Mzk1PaperFaithful312NormedActual.final_3_12_normed' depends on axioms: [propext, Classical.choice, Quot.sound]
'...Mzk1PaperFaithful312RpNormalizationActual.rpVolume_rpRegion_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'...Mzk1PaperFaithful312RpNormalizationActual.hqneg_direct' depends on axioms: [propext, Classical.choice, Quot.sound]
'...Mzk1PaperFaithful312HqnegActual.hqneg_iff_rpVolume_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'...Mzk1PaperFaithful312FinalActual.final_3_12_concrete' depends on axioms: [propext, Classical.choice, Quot.sound]
'...Mzk1PaperFaithful312FinalActual.final_3_12_concrete'' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Gate file: `Mzk1PaperFaithful312GateRecordActual.lean` (EXIT=0, olean=True).

No RETRACTED statement is referenced.  The normalized route has NO named hqneg
hypothesis; only the paper normalization convention (denominator = fullRegion, a
ratio-only choice) and the standard IPL/SHE/APT evidence parameters remain.
