# DECOMP-R-LOCAL — local expansion of R = -rhs (A991)

Status: symbolic decomposition; no new Lean file compiled.  Signs marked with their
Lean sources; entries marked UNKNOWN-DEPENDENT where the sign depends on theta values.

## 0. Global chain

`R = -rhs`, `rhs = RHSData.rhs = R.vol.processionVol R.thetaHull`
(`Iut/Cor312/RightHandSide.lean:107`).

`processionVol R = (∑ i : Fin D.proc.length, globalVol (R i)) / D.proc.length`
(`Iut/Cor312/LogVolume.lean:207`).  Here `D.proc.length = ℓ* = (ℓ-1)/2`;
the capsule index is `i : Fin (nC D)`.

`globalVol (R i) = ∑ᶠ vQ, packetVol i vQ ((R i).region vQ)`
(`LogVolume.lean:177`).

`packetVol_product` (`LogVolume.lean:130`), for nonempty components:
`packetVol i vQ (productRegion U) =
  ∑ c, (∏ j, weight vQ (c j)) * componentVol i vQ c (U c)`,
with `packetWeight i vQ c := ∏ j, weight vQ (c j)` (`:141`),
`packetWeight_pos` (`:153`), `weight_sum_one` (`:88`).

So the elementary index set is `(vQ, i, c, j)` with `j` ranging over the labels
of capsule `i` (`c : Lab i → Fiber vQ`, component tuple).

## 1. Per-place packet term

At rational place `vQ`, capsule `i`, component `c`:
  `P_{i,vQ,c} := packetWeight i vQ c * componentVol i vQ c (U_{i,vQ,c})`,
where `U` is `R.thetaHull`'s component (`RHSData.thetaHull = R.hull.hullFamily
R.thetaPilot`, `RightHandSide.lean:99`).

Then
  `rhs = (1/nC) ∑_i ∑_vQ ∑_c P_{i,vQ,c}`
and `R = -(1/nC) ∑_i ∑_vQ ∑_c P_{i,vQ,c}`.

Signs: `packetWeight > 0` (PROVED, `packetWeight_pos`); `componentVol` sign is
the local content below.

## 2. Finite place: p != 2 and tame

`componentVol i (.finite p) c` at a tame prime (`p` odd, every e_cj ≤ p-2):
`componentVol_leastHull_tensorLogShell_eq_tame`
(`Iut/WallEquiv/VcI.lean:435`, imported from lana root tree):
  `componentVol(leastHull(tensorLogShell)) = ∑_j (1 - 1/e_cj) * log p`
(nonnegative; each `e_cj ≥ 1`).

For the theta hull, the theta scaling by `q^{j²}` enters through `scaleElt`
(paper q-side; `D.scaleElt`): the hull of the scaled shell is the scaled hull
(units scaling preserves least hull; `leastHull_units_smul`).  The scaling law
for `componentVol` gives the negative q term
  `- ∑_j j² · ord_p(q) · log p`
(up to the paper normalization by `(2ℓ)` in `A_p = ord_p(q) log p/(2ℓ)`;
in terms of `A_p` this is `-∑_j (2ℓ) j² A_p`).
Sign: NEGATIVE for ord_p(q) > 0 (contracting q); this is the local `-A_v` piece.

`ind2Term` (`Iut/WallEquiv/Gap.lean:747`) is EXACTLY the difference
`componentVol(leastHull(thetaComponent)) - componentVol(scaleElt • leastHull(shell))`
and is NONNEGATIVE (`ind2Term_nonneg`, `Gap.lean:756`); it is the positive
Ind2 buffer.  `gapHullAt (finite p) = ∑_c w_c ind2Term` (`Gap.lean:895`).

At wild/ramified primes the exact hull radius is `logShellRadius`
(`Iut/WallEquiv/VcI.lean:464`),
`hullPacket_finite = ∑_c w_c ∑_j logShellRadius(...) * log p` (`:806`);
sign of `logShellRadius` in the theta hull is the same positive shell term plus
the negative q-scaling; the wild correction relative to tame is UNKNOWN-DEPENDENT
(needs `e`, ramification, `p=2` data).

## 3. Archimedean place

`componentVol` at `∞` is normalized by `componentVol_archBall = 0`
(`LogVolume.lean:114`).  The archimedean scaling law is
`componentVol_arch_scale t = log t` (`Iut/Concrete/LocalConstruct/Volume.lean:252`).

The theta hull arch component contributes a sum of `log` of theta scales
(Gaussian/theta values); sign: UNKNOWN-DEPENDENT on the values (`log q^{j²}`
negative for q<1; `log` of `>1` scales positive).
`archDefect` (`Iut/WallEquiv/VcI.lean:653`/Gap `gapHullAt ∞ = 0`) is the positive
defect of the arch log-shell against its polydisc; it is the positive buffer
(`archDefect_nonneg`, `VcI.lean`).

## 4. L-chain volume (A989) vs lana rhs

`thetaHullVolumeAtL` and `globalThetaHullLogVolumeL` use
`sourceSetVolume v (sourceHolomorphicHull v R n)` (`GlobalThetaPilotHullLogVolumeActual:46`):
- `sourceSetVolume v S = ⨆_{x∈S} ENNReal.ofReal (sourceLocalLogDegree v x)`
  (`SourceImageHullVolume.lean:188`);
- `sourceLocalLogDegree v x = ∑ i, logDegreeAt 0 0 v (x i)` (`:104`);
- `logDegreeAt n m v x = toAdd ((I.primeStripAt n m).degree v x)`
  (`SourceImageHull.lean:100`).

These are **logarithmic set volumes**, not `RHSData.vol.processionVol`; no theorem
identifies `-globalThetaHullLogVolumeL` with `R = -rhs`.  This is a top-level GAP
of the L-chain (it would require a comparison of the source-set-volume Haar model
with the C3 `componentVol`/`packetVol` Haar model).

## 5. Sign summary

| term | formula/shape | sign | source |
|---|---|---|---|
| `packetWeight` | ∏_j weight | > 0 | `LogVolume.lean:153` |
| tame shell | Σ_j (1-1/e_cj) log p | ≥ 0 | `VcI.lean:435` |
| Ind2 | `ind2Term` | ≥ 0 | `Gap.lean:756` |
| q-scaling (finite) | -∑_j j² ord_p(q) log p | ≤ 0 for ord>0 | scaling law/`scaleElt`; paper q |
| wild hull radius | Σ_j logShellRadius log p | UNKNOWN-DEPENDENT | `VcI.lean:464/806` |
| arch theta volume | Σ log(theta scales) | UNKNOWN-DEPENDENT | `Volume.lean:252` |
| arch defect | `archDefect` | ≥ 0 | `VcI.lean` arch defect |
| `-A_v` | `-ord_p(q)logp/(2ℓ)` per bad v | negative | `Cor312/LeftHandSide.lean:88` |

## 6. What remains to prove

1. The scaling law identifying the theta-hull finite component with
   `hullPacket +/- j²` q terms (partially in `ind2Term` definition; exact sign
   normalization by `(2ℓ)` needs the paper q-value convention).
2. The identification of the source-set-volume R with `RHSData.vol` (top-level GAP).
3. The wild `logShellRadius`/2-adic and arch theta-value data (A978/A983 gaps).

All items are symbolic here; no numerical R is claimed.
