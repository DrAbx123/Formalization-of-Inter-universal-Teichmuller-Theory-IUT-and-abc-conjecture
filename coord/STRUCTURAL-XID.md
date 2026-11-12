# STRUCTURAL-XID — the xi-d determinant statement as a structure (A1084)

Status: design only; no compile.  Paper source: IUT III, Step (xi-d),
III:10837-10865 (quoted in `coord/IUT-TEXT-N5.md`).

## 1. The paper statement (structure-level)

From III:10834-10865:
- the localizations of arithmetic vector bundles are of **rank > 1**;
- the q-pilot object is a **rank-one** arithmetic line bundle;
- one forms a suitable positive tensor power of the **determinant** of the
  localizations;
- applies the log-volume, normalized with respect to `j ∈ F_l`, to two
  regions: `1,◦U` (the theta hull) and the q-pilot region;
- obtains `R_{≤−|log Θ|} ⊆ R` and `−|log q| ∈ R`.

## 2. Objects and morphisms

Paper objects:
```text
L_{i,v}        rank>1 arithmetic vector bundle localization (local system)
det L          ⋀^{r} L, rank-one determinant line bundle
(det L)^{⊗k}   positive tensor power (k ≥ 1)
qBundle        rank-one arithmetic line bundle of the q-pilot
μ^log(-)       normalized (procession/j-normalized) log-volume on the
               log-shell region
```
Morphism: a comparison between the determinant line bundle `(det L)^{⊗k}` and
`qBundle`, preserving the normalized log-volume (or producing the two-ray
inclusion).  It is not an equality of rank>1 bundles.

## 3. Three structural forms

### Form A — morphism existence (paper-literal)
```lean
structure XIDDeterminantComparison where
  detBundle : RankOneLineBundle
  qBundle : RankOneLineBundle
  k : Nat
  k_pos : 0 < k
  morphism : detBundle → qBundle          -- or qBundle → detBundle
  normLog_eq : normalizedLogVolume detBundle =
    normalizedLogVolume qBundle + const
  region : Set Block
  region_eq : region = thetaHullRegion
```
Needs a rank>1 determinant construction and a rank-one comparison; the
determinant side is available only on the HDD carrier (`S1476/S1418/S1422`),
not on C3.

### Form B — region inclusion
```lean
structure XIDRegionComparison where
  thetaRegion : Set Block
  qRegion : Set Block
  theta_subset_q : thetaRegion ⊆ qRegion
  vol_theta : normLogVolume thetaRegion = -R
  vol_q : normLogVolume qRegion = -A
```
`haarLogVolume_mono` + the signed/negative normalization turn the inclusion
into `-A ≤ -R`.  This is the abstract skeleton of
`Mzk1QRegionInclusionActual` / `Mzk1XiEContainmentRequirementActual`;
the concrete theta/q region identification is the GAP.

### Form C — line-bundle comparison (rank-one)
```lean
structure XIDLineBundleComparison where
  detBundle : LineBundle (k := K)      -- rank-one fractional ideal
  qBundle : LineBundle (k := K)
  det_logVol : Real
  det_logVol_eq : det_logVol = globalLogVolume detBundle
  q_logVol : Real
  q_logVol_eq : q_logVol = globalLogVolume qBundle
  comparison : det_logVol ≤ q_logVol    -- or the reversed/with constant
```
`DeterminantLogVolumeActual` supplies `LineBundle`, `determinantLine`,
`determinantNorm`, `globalLogVolume`, `localizedLine`, `localizedLine_mono`.

## 4. Which form is most formalizable with current material?

| form | current assets | missing | verdict |
|---|---|---|---|
| A morphism | S1476 rank>1 bundle, S1418 global lattice, S1422 det data; `LineBundle` rank-one | rank>1 determinant on C3, morphism of line bundles, normalized log-volume comparison | large; not first |
| B region inclusion | `haarLogVolume_mono`, `Mzk1QRegionInclusionActual`, `S2807` theta-hull volume identity | concrete theta/q region identification, two volume identities | medium; abstract skeleton green |
| C line-bundle comparison | `DeterminantLogVolumeActual` rank-one API, `S2735/S2736` q-pilot line bundle, `S2807` theta hull volume | identification `detBundle = qPilotLineBundle`, `det_logVol = theta hull log-volume` | **most likely first** |

Recommendation: formalize **Form C** first (rank-one line-bundle comparison),
then connect it to Form B (region inclusion) via `S2807` and a region/log-volume
identification.  Form A is the literal paper determinant and remains a later
port.

## 5. Required definitions (checklist)

Rank-one / line bundle (green or available):
- `LineBundle k := FractionalIdeal (nonZeroDivisors O_k) k`;
- `determinantLine I := I`;
- `determinantNorm I := FractionalIdeal.absNorm I`;
- `globalLogVolume I := Real.log (determinantNorm I)`;
- `localizedLine I v`, `localizedLine_mono`;
- `sectionLogVolume` (`DeterminantLogVolumeActual:155`).

q-pilot side:
- `qPilotIdeal`, `qPilotLineBundle`, `qPilotLineBundleExtended`
  (`S2735QPilotLineBundleActual:23/35/87`);
- `S2736QPilotLineBundleLogVolume` (`S2736...:19`).

Rank>1 determinant (HDD):
- `S1476RankArithmeticVectorBundle`, `S1476ArithmeticVectorBundleLocalization`,
  `s1476ActualLocalization` (`S1476:82/219/232`);
- `S1418GlobalLattice`, `s1418GlobalLattice_eq_hull`, `s1418DetTensorPower_*`;
- `S1422.DetTensorPowerLogVolumeBookkeeping`, `detDataOfHull`,
  `dependentDetDataOfChar`, `hullPacket_det_eq_prod`,
  `hullPacket_logVolume_eq_log_det`.

Normalized log-volume:
- `arithmeticTupleNormalizedLogVolume`/`_mono`
  (`FinitePlaceNormalizedUnitScalingLogVolume:107/379`);
- `dependentHullLogVolume` (`S1422`);
- `S2807_thetaHullVolume_eq_haarRegion` (`S2807...:40`);
- `S2717ThetaHullLogVolume` (`S2717...:50`).

## 6. Port dependencies (Gap/VcI/ThetaRegion/LocalTheory wave)

Per `coord/LANA-DECL-CHECKLIST.md`:
- `componentVol`, `incl`, `factorAut/tensorAut/indAut`: batch **L** (LocalConstruct);
- `leastHull`, `logShellRadius`, `scaleEltAt/scaleElt`, `ordp_qrootOf`,
  `vcI/vcIComp`: batch **C** (copy-only);
- `hullPacket`, `vcIPacket`: batch C;
- `DeterminantLogVolumeActual`, S2735/S2736, S1422: already in our tree (green).

Form C needs no new lana port beyond the rank-one `DeterminantLogVolumeActual`
and the q-pilot line-bundle files; only the identification with the actual
theta hull volume (S2807) is a bridge.

## 7. Minimal Lean statement draft (Form C)

```lean
structure XIDLineBundleComparison (k : Type) [Field k] [NumberField k] where
  detBundle : LineBundle (k := k)
  qBundle : LineBundle (k := k)
  det_logVol : Real
  det_logVol_eq : det_logVol = globalLogVolume detBundle
  q_logVol : Real
  q_logVol_eq : q_logVol = globalLogVolume qBundle
  comparison : det_logVol ≤ q_logVol
```
with the actual instantiations:
`detBundle := qPilotLineBundle` (or a determinant line),
`qBundle := qPilotLineBundle`, and the comparison supplied by the
(still missing) actual theta/q volume identities.

## 8. Verdict

- The decisive xi-d item is a **rank-one determinant/line-bundle comparison**,
  not a rank>1 equality.
- Form C is the best first target; Form B is its region-level counterpart;
  Form A is the literal paper morphism and needs the rank>1 C3 bridge.
- No fake morphism/rank>1 determinant is introduced; the missing pieces are
  the C3 determinant bridge and the theta/q volume identities.
