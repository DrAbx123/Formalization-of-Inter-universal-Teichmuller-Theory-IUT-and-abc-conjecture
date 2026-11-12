# N5-XID-PAPER-VS-OURS — Step (xi-d) vs our CTheta/hscalar (A1042)

Status: read-only comparison; no compile.  Sources: `coord/IUT-TEXT-N5.md`
(IUT III p. 181-183) and our `tmp/sheaf/xif/paper` files.

## 1. Paper Step (xi-d), D-numbered (IUT III pp. 183-184)

Source line anchors are global `III.txt` lines; D19-D23 extend the D-numbering of
`coord/IUT-TEXT-N5.md`.

**D19 (xi-d conclusion, III:10825-10833).**
> (xi-d) The discussion of (xi-c) thus yields the following conclusion:
> The multiradial construction algorithm of Theorem 3.11, followed by for-
> mation of the holomorphic hull, yields a collection of possibilities of out-
> put data in 1,◦U that are linked/related [cf. (IPL)], via isomorphisms
> of F⊩▶-prime-strips, to the representation [via the log-Kummer cor-
> respondence in the 1-column] of the q-pilot object at (1,0) on 1,◦UQ,
> and, moreover, whose construction may be expressed entirely relative to
> localizations of arithmetic vector bundles over rings that arise in
> the arithmetic holomorphic structure in the 1-column [cf. (SHE)].

**D20 (rank > 1 and determinant, III:10834-10840).**
> Here, we observe that these “localizations of arithmetic vector bundles” are [unlike
> the arithmetic line bundle that gives rise to the q-pilot object] of rank > 1. Moreover,
> the q-pilot object is defined at the level of realifications of Frobenioids of [global]
> arithmetic line bundles. Thus, it is only by forming [a suitable positive tensor power
> of] the determinant of the localizations of arithmetic vector bundles mentioned in
> the above display [cf. Remark 3.9.5, (vii), (Ob3), (Ob4)] and then applying the
> [suitably normalized, with respect to j∈|F_l|] log-volume to various regions —

**D21 (the two regions, III:10840-10843).**
> i.e., the region 1,◦U and the region that arises from the representation of the q-pilot
> object at (1,0) on 1,◦UQ — in 1,◦UQ [cf. Remark 3.9.5, (vii), (Ob3), (Ob4), (Ob6),
> (Ob7), (Ob9)], that we are able to obtain completely comparable objects [cf.
> Remarks 3.9.5, (vii), (Ob5), (Ob6), (Ob7), (Ob8), (Ob9); 3.9.5, (viii), (ix)], namely,

**D22 (the comparison display, III:10844-10851).**
> R_{≤−|log(Θ)|}
> def
> = {λ∈ R | λ≤−| log(Θ)|} ⊆ R;   −| log(q)|∈ R
> — where we recall that, by definition, −|log(Θ)| is the [negative—cf. the discussion
> of “possible images” at the beginning of the present proof] log-volume of 1,◦U, while
> −| log(q)| is the log-volume of the region that arises from the representation of
> the q-pilot object at (1,0) on 1,◦UQ.

**D23 (interpretation as global arithmetic degrees, III:10851-10855).**
> In this context, it is useful to recall from
> Proposition 3.9, (iii) [cf. also the discussion of Remarks 3.9.2, 3.9.6], that global
> arithmetic degrees of objects of global realified Frobenioids may be interpreted
> as log-volumes [cf. also the discussion of Remarks 1.5.2, (iii); 3.10.1, (iv), as
> well as of Remark 3.12.2, (v), below].

**D24 (vertical shift/rectification, III:10855-10865).**
> Finally, in this context, we observe [cf.
> the first display of the present (xi-d)] that it is of crucial importance to apply
> the log-Kummer correspondence in the 1-column [cf. the discussion of log-
> Kummer correspondences in Remark 3.9.5, (vii), (Ob7), (Ob8); Remark 3.9.5, (viii),
> (sQ4); Remark 3.9.5, (ix); the final portion of Remark 3.9.5, (x); the discussion
> of the final portion of Remark 3.12.2, (v), below], in order to rectify the vertical
> shift/mismatch [cf. the discussion of (iii), (iv) in the case of the 0-column] between
> the unit portion of 1,0F⊩▶×μ_∆ and the log-shells arising from [the image via the
> relevant Kummer isomorphisms of] this unit portion, which give rise to the tensor
> packets of log-shells that constitute 1,◦U.

Continuation (xi-e, p. 184, III:10866-10880) restates that the relationship between
`−|log(q)|` and the input prime-strip is the one prescribed by the arithmetic
holomorphic structure in the 1-column and by (SHE).

## 2. Our definitions found by grep

| file | declaration | signature/role |
|---|---|---|
| `S2691ExactQNormalizationActual.lean` | `qNormFactor (l)` | `1/(2·l.value)` |
| | `paperQAbsLog l logQ` | `qNormFactor l * logQ` = `|log q|` normalization |
| | `cThetaBracket l logQ dmod dFpd fFpd eStar etaPrm` | bracket `{...}` of IUT IV p. 23 |
| | `CTheta l logQ dmod dFpd fFpd eStar etaPrm` | `((l+1)/4 * paperQAbsLog)*cThetaBracket - 1` (printed CTheta) |
| `S2715CThetaPaperScaleActual.lean` | `CThetaPaper l logQ ...` | `(((l+1)/4)/paperQAbsLog)*cThetaBracket - 1` |
| | `CThetaPaper_eq_S2691CTheta_scale` | `CThetaPaper = (CTheta+1)/(paperQAbsLog)^2 - 1` |
| | `CThetaPaper_ge_neg_one_iff` | `CThetaPaper≥-1 ↔` Theorem 1.10 bracket inequality |
| | `CThetaPaper_lowerBound_of_thetaHull_upper` | `theta≤CThetaPaper*|logq|` + `-|logq|≤theta` ⇒ `-1≤CThetaPaper` |
| | `CThetaPaper_lowerBound_of_paperAbsLog` | same with `|logq|=paperQAbsLog` |
| `S2714CThetaUpperInventoryActual.lean` | `S2714_sourceSignedHull_upper_zero` | `sourceSignedHullLogVolume ≤ 0*|logq|` (trivial upper) |
| | `S2714_cThetaLowerBound_of_upper` | abstract `theta≤C*|logq|` + `-|logq|≤theta` ⇒ `-1≤C` |
| `S2807SG3bScalarActual.lean` | `S2807_upperGap_of_packetLogVolume_le` | assumes `hpacket` and `hscalar : -packetLogVolume ≤ CThetaPaper*paperQAbsLog` |
| `S2819ScalarBracketActual.lean` | `S2819_scalar_iff_CTheta_ge` | `-packetLogVolume≤CThetaPaper*A ↔ -packetLogVolume/A≤CThetaPaper` |
| | `S2819_scalar_iff_neg_one_of_packet_eq` | if `packetLogVolume=A`, scalar iff `-1≤CThetaPaper` |
| | `S2819_scalar_iff_bracket_of_packet_eq` | same iff Theorem 1.10 bracket inequality |

Other determinant-related files:
- `DeterminantLogVolumeActual.lean`: `determinantLine`, `determinantNorm`,
  `globalLogVolume` for a rank-one line bundle; this is a **rank-one** determinant,
  not the paper's `det` of rank>1 localizations;
- `ArithmeticLineBundleActual.lean`: actual line bundle, `actualDeterminantData`,
  `determinantLine_eq`;
- `DetNormalizationObjectActual.lean`: packet `matrixLogDet`, `packetLogVolume`,
  `packetDet`;
- `Hull06DetTensorActual.lean`: H5 det tensor bookkeeping;
- `S2807ThetaHullVolumeIdentityActual.lean`: `S2717UpperGap` and the tensor
  log-volume identity target.

## 3. Item-by-item correspondence

| paper (xi-d) | ours | status |
|---|---|---|
| holomorphic hull of union of possible Θ-pilot images, log-volume `−|log Θ|` | `sourceSignedHullLogVolume` / `thetaLogVolume` in `S2714`, `S2715` | **identification missing**; paper is procession-normalized hull of union; ours is a positive/negative signed hull-volume API, no theorem `sourceSignedHullLogVolume = rhs` |
| q-pilot region log-volume `−|log q|` | `paperQAbsLog l logQ` (formal real parameter) | **identification missing** to `I.qPilotSignedLogVolume`/global q-pilot data; no theorem `paperQAbsLog = |qPilotSignedLogVolume|` |
| `det(localizations of arithmetic vector bundles)^{⊗k}` | `C3LogShellTensorBlock` / `actualC3LogShellTensorLogVolume` (`S2807`) | `hpacket : actual... = packetLogVolume` is an **explicit hypothesis** in S2807, not a theorem; the rank>1 determinant comparison is not formalized |
| log-volume comparison `−|log Θ| ≤ CΘ·|log q|` | `CThetaPaper_lowerBound_of_thetaHull_upper` / `hscalar` | uses `CThetaPaper`, not `CTheta`; see §4 scale issue; `hscalar` remains an explicit hypothesis in S2807 |
| `C_Θ` printed formula | `CTheta` (S2691) is the printed formula | matches paper p. 23; but our consumers use `CThetaPaper` |
| `R_{≤−|log Θ|} ⊆ R` / `−|log q| ∈ R` | abstract real inequality `-|logq| ≤ theta` in `S2714`/`S2715` | the real-ray inclusion is represented by `hincl`; no construction of the region `R_{≤}`. **Direction note (A1049)**: the sufficient region inclusion is `thetaRegion ⊆ qRegion` (with `logVol=-log μ`), not the opposite; the opposite gives the reversed inequality. |
| `1/6 log(q) ≤ ...` final bound | `CThetaPaper_ge_neg_one_iff` / `S2819_scalar_iff_bracket_of_packet_eq` | gives the bracket inequality, equivalent to `CThetaPaper≥-1`; not yet connected to the paper's final `1/6 log q ≤ ...` without the CTheta scale bridge |

## 4. Scale issue: `CThetaPaper` vs printed `CTheta`

Paper (IUT IV p. 23, Theorem 1.10):
```
CTheta = ((l+1)/4) * |log q| * bracket - 1,
A := |log q| = paperQAbsLog l logQ.
```
Ours:
```
CTheta      = ((l+1)/4) * A * bracket - 1         (S2691, printed formula)
CThetaPaper = ((l+1)/4 / A) * bracket - 1         (S2715)
CThetaPaper = (CTheta + 1) / A^2 - 1              (S2715 theorem)
```
Hence
```
CThetaPaper * A = (CTheta + 1)/A - A,
```
which is **not** `CTheta * A` unless `(CTheta+1)/A - A = CTheta*A`, i.e. only under
a very special algebraic relation that is not proved and is generally false.

Consequence:
- `S2807 hscalar` is `-packetLogVolume ≤ CThetaPaper * A`, not
  `thetaLogVolume ≤ CTheta * A`; it is a different scalar inequality.
- `CThetaPaper_ge_neg_one_iff` and `CThetaPaper_lowerBound...` do establish the
  **same bracket inequality** as `CTheta ≥ -1` (because both `CThetaPaper≥-1`
  and `CTheta≥-1` are equivalent to the same bracket inequality), so the
  lower-bound target is not lost.
- But an upper-bound derivation phrased with `CThetaPaper` cannot be quoted as
  the paper's `theta ≤ CTheta*|logq|`; a bridge lemma or a switch of the consumer
  to `CTheta` is needed.

## 5. Missing identifications (GAP list)

1. **GAP-XID-1 (hull/Θ identification).** `sourceSignedHullLogVolume` (or the
   positive hull log-volume used in our chain) equals the paper's
   `−|log Θ|` (procession-normalized log-volume of the hull of the union under
   Ind1/Ind2/Ind3).  No theorem in the grepped files.
2. **GAP-XID-2 (q identification).** `paperQAbsLog l logQ = |qPilotSignedLogVolume|`
   for the concrete q-pilot; no theorem connects the formal `logQ` to the actual
   `I.qPilotSignedLogVolume`/global q-pilot reads.
3. **GAP-XID-3 (determinant).** The paper's `det` of rank>1 localizations
   (positive tensor power) equals the determinant underlying our packet log-volume;
   `S2807` assumes `actualC3LogShellTensorLogVolume = packetLogVolume` as `hpacket`,
   and the rank>1 determinant comparison is not in `DeterminantLogVolumeActual`
   (which is rank-one).
4. **GAP-XID-4 (CTheta scale).** Connect `CThetaPaper*A` to `CTheta*A` (or replace
   `hscalar` by the printed `CTheta` version).  Exact relation is
   `CThetaPaper+1 = (CTheta+1)/A²`.
5. **GAP-XID-5 (ray/region).** Paper's `R_{≤−|log Θ|}` region inclusion is encoded
   as the real inequality `-|logq| ≤ theta`; no construction of the region or of
   the comparison map is needed for the scalar bound, but the geometric statement
   of xi-d is not formalized.
6. **GAP-XID-6 (final 1/6 bound).** To get the paper's final
   `(1/6)log(q) ≤ ...`, one must use the printed `CTheta` formula (S2691), not
   only the CThetaPaper bracket equivalence; S2819 gives the bracket equivalence
   but not the final inequality with the exact constants.

## 6. Shortest repair path

- Use `CTheta` (S2691) for the scalar upper bound:
  `thetaLogVolume ≤ CTheta l logQ ... * paperQAbsLog l logQ`;
  then `S2714_cThetaLowerBound_of_upper` directly gives `-1 ≤ CTheta`.
- Keep `CThetaPaper` only as an auxiliary normalization; if used, add
  a bridge theorem comparing the two scalar inequalities (not currently present).
- Prove GAP-XID-3 (det packet identity) and GAP-XID-1/2 (hull/q identifications)
  before claiming the paper's xi-d comparison; otherwise state them as explicit
  hypotheses (as S2807 already does for `hpacket` and `hscalar`).

---

## 7. Direction correction (A1049)

> The sufficient geometric direction is **`thetaRegion ⊆ qRegion`**, not `qRegion ⊆ thetaRegion`.
> Reason: with `logVol S = -log μ(S)`, `theta ⊆ q` ⇒ `logVol q ≤ logVol theta`;
> writing `logVol q = -A`, `logVol theta = -R` gives `-A ≤ -R`, i.e. the Cor 3.12 form.
> The reverse inclusion would yield `-A ≥ -R`.  This affects only the sign of the
> region-inclusion subgoal, not the determinant algebra or the CTheta formulas.
>
> **A1050 confirmation**：四步推导为 (1) `logVol=-log μ`，`-A=-|log q|`、`-R=-|log Θ|`；
> (2) variant `-A≤-R ⇔ A≥R`；(3) `A=log μ(q)`、`R=log μ(theta)`，log 严格单调 ⇒ `A≥R ⇔ μ(q)≥μ(theta)`；
> (4) measure 单调只给**单向** `thetaRegion⊆qRegion ⇒ μ(theta)≤μ(q)`，故 `thetaRegion⊆qRegion` 是**充分条件，不是等价**；反向包含只给 `-A≥-R`。此前 A1048b 的 `q⊆θ` 说法**作废**。
