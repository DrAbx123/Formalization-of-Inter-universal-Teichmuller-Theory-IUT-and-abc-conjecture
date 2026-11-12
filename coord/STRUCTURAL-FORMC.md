# STRUCTURAL-FORMC — rank-one line-bundle comparison (A1085)

Status: partial Lean file written; no compile.

## 1. Exact Form C statement

Let `qBundle` and `detBundle` be rank-one line bundles over `K`
(`LineBundle (k:=K) = FractionalIdeal (nonZeroDivisors O_K) K`).
Write
```
A := globalLogVolume qBundle / (2ℓ),
R := globalLogVolume detBundle / (2ℓ).
```
Then
```
globalLogVolume detBundle ≤ globalLogVolume qBundle
```
implies `R ≤ A`, hence `-A ≤ -R`, i.e. `−|log q| ≤ −|log Θ|`.

This is the rank-one shadow of paper xi-d: the determinant of the rank>1
localizations is compared with the q-pilot line bundle; the comparison is a
`≤` of normalized log-volumes, not a ring equivalence.

## 2. Lean file

`tmp/sheaf/xif/paper/Mzk1StructuralLineBundleActual.lean`:
- `FormCLineBundleComparison l K`: fields `qBundle`, `detBundle`, `A`, `R`,
  `hA`, `hR`, `hcmp`;
- `FormCLineBundleComparison.neg_A_le_neg_R` **PROVED**:
  `-A ≤ -R` from `hcmp`, using `2ℓ > 0` and division monotonicity;
- `QK l := (S2735Arithmetic l).K`;
- `qPilotLineBundleC l : LineBundle (k := QK l) := qPilotLineBundle l`;
- `QPilotGlobalLogBridge l A : Prop` (`A = globalLogVolume qBundle/(2ℓ)`);
- `ThetaDetGlobalLogBridge l detBundle R : Prop`
  (`R = globalLogVolume detBundle/(2ℓ)`);
- `S1487FormCData l : Prop` (exists detBundle/A/R with the two bridges and
  `hcmp`);
- `S1487FormC_variant l (h : S1487FormCData l) : ∃ A R, -A ≤ -R` **PROVED**
  conditionally.

## 3. Bridge lemmas needed

1. **q-pilot bridge**
   `QPilotGlobalLogBridge l A`.
   The q-pilot line bundle is `qPilotLineBundle l`
   (`S2735QPilotLineBundleActual:35`), an ideal/fractional ideal;
   `S2736QPilotLineBundleLogVolume` computes `log(absNorm ...)`, but no theorem
   identifies it with `A = qOrder·logp/(2ℓ)` or `sourceQPilotSignedLog`.
2. **theta/determinant bridge**
   `ThetaDetGlobalLogBridge l detBundle R`.
   `DeterminantLogVolumeActual.globalLogVolume` is a rank-one norm log;
   `S2807_thetaHullVolume_eq_haarRegion` identifies the theta hull log-volume
   with `-Haar` of the C3 tensor region, **not** with a line-bundle norm.
3. **determinant line**
   `detBundle` must be the determinant of the rank>1 localizations.  The HDD
   assets (`S1476/S1418/S1422`) construct rank>1 determinants, but on the
   dependent-product carrier, not on the C3 tensor block.
4. **normalization**
   `globalLogVolume` is `log(absNorm I)`, positive on `qPilotIdeal`
   (norm `5·5·2161·2161`); `A` is `logQ/(2ℓ)` and signed negative.  The
   `/(2ℓ)` and the identification of `logQ` with the line-bundle norm are
   exactly the missing normalization.

## 4. What is proved vs what is GAP

| item | status |
|---|---|
| `FormCLineBundleComparison` fields | DEF |
| `-A ≤ -R` from `hA/hR/hcmp` | **PROVED** |
| `QPilotGlobalLogBridge` | GAP (Prop) |
| `ThetaDetGlobalLogBridge` | GAP (Prop) |
| `S1487FormCData` | GAP (Prop) |
| `S1487FormC_variant` | **PROVED conditional** |

## 5. Which line bundle to which?

The comparison is
```
det(rank>1 localizations)^{⊗k}    ≤    qPilotLineBundle
```
in normalized global log-volume.  In the rank-one specialization
`detBundle` may be taken to be a determinant line `⋀^r L`, while `qBundle` is
the q-pilot fractional ideal.  The Lean file keeps both as `LineBundle` and
records the comparison as an inequality of `globalLogVolume`.

## 6. Verdict

- Form C is arithmetically closed: the line-bundle comparison proves
  `-A ≤ -R`.
- The missing geometric/normalization data are the two bridge Props and the
  determinant line identification; no fake equality is introduced.
- This is the most formalizable form; Form A (rank>1 morphism) and Form B
  (region inclusion) remain later.
