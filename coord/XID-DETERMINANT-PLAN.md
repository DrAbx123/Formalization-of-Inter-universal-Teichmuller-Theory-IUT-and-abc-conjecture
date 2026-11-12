# XID-DETERMINANT-PLAN — Step (xi-d), rank-one and rank>1 determinant (A1044)

Status: read-only plan; no compile.

## 1. Step (xi-d) full original, D19-D24 (IUT III:10825-10865)

Continuous OCR from `coord/IUT-TEXT/III.txt`; global line numbers in brackets.

```text
[10825] (xi-d) The discussion of (xi-c) thus yields the following conclusion:
[10826] The multiradial construction algorithmof Theorem 3.11, followed by for-
[10827] mation of theholomorphic hull, yields a collection of possibilities of out-
[10828] put data in1,◦U that arelinked/related [cf. (IPL)], viaisomorphisms
[10829] of F⊩▶-prime-strips, to the representation [via the log-Kummer cor-
[10830] respondence in the 1-column]o ft h eq-pilot object at (1,0) on 1,◦UQ,
[10831] and, moreover, whose construction may be expressed entirely relative to
[10832] localizations of arithmetic vector bundlesover rings that arise in
[10833] the arithmetic holomorphic structurein the 1-column [cf. (SHE)].
[10834] Here, we observe that these “localizations of arithmetic vector bundles” are [unlike
[10835] thearithmetic line bundlethatgivesrisetothe q-pilot object]of rank> 1. Moreover,
[10836] the q-pilot object is deﬁned at the level ofrealiﬁcationsof Frobenioids of [global]
[10837] arithmetic line bundles. Thus, it is only by forming [a suitable positive tensor power
[10838] of] the determinant of the localizations of arithmetic vector bundles mentioned in
[10839] the above display [cf. Remark 3.9.5, (vii), (Ob3), (Ob4)] and then applying the
[10840] [suitably normalized, with respect toj∈| Fl|] log-volume to various regions —
[10841] i.e., theregion1,◦U and theregionthat arises from the representation of theq-pilot
[10842] object at (1,0) on1,◦UQ —i n1,◦UQ [cf. Remark 3.9.5, (vii), (Ob3), (Ob4), (Ob6),
[10843] (Ob7), (Ob9)], that we are able to obtaincompletely comparable objects [cf.
[10844] Remarks 3.9.5, (vii), (Ob5), (Ob6), (Ob7), (Ob8), (Ob9); 3.9.5, (viii), (ix)], namely,
[10845] R≤−|log(Θ)|
[10846] def
[10847] ={λ∈ R| λ≤−| log(Θ)|} ⊆R; −| log(q)|∈ R
[10848] —wherewerecallthat, bydeﬁnition, −|log(Θ)|isthe[ negative—cf. thediscussion
[10849] of “possible images”at the beginning of the present proof] log-volume of1,◦U, while
[10850] −| log(q)| is the log-volume of the region that arises from the representation of
[10851] the q-pilot object at (1,0) on 1,◦UQ. In this context, it is useful to recall from
[10852] Proposition 3.9, (iii) [cf. also the discussion of Remarks 3.9.2, 3.9.6], thatglobal
[10853] arithmetic degrees of objects of global realiﬁed Frobenioids may be interpreted
[10854] as log-volumes [cf. also the discussion of Remarks 1.5.2, (iii); 3.10.1, (iv), as
[10855] well as of Remark 3.12.2, (v), below]. Finally, in this context, we observe [cf.
[10856] the ﬁrst display of the present (xi-d)] that it is ofcrucial importance to apply
[10857] the log-Kummer correspondence in the 1-column [cf. the discussion of log-
[10858] Kummer correspondencesin Remark 3.9.5, (vii), (Ob7), (Ob8); Remark 3.9.5, (viii),
[10859] (sQ4); Remark 3.9.5, (ix); the ﬁnal portion of Remark 3.9.5, (x); the discussion
[10860] of the ﬁnal portion of Remark 3.12.2, (v), below], in order torectify thevertical
[10861] shift/mismatch[cf. thediscussionof(iii), (iv)inthecaseofthe0 -column]between
[10862] the unit portion of 1,0F⊩▶×μ
[10863] ∆ and thelog-shells arising from [the image via the
[10864] relevant Kummer isomorphisms of] this unit portion, which give rise to thetensor
[10865] packets of log-shellsthat constitute1,◦U.
```

Continuation (p. 184, III:10866-10880) is (xi-e): the relationship between
`−|log(q)|` and the input prime-strip is exactly the one prescribed by the
1-column arithmetic holomorphic structure / (SHE).

**Displays in this range:**
- D20: rank>1 localizations; determinant positive tensor power (III:10834-10840);
- D21: two regions `1,◦U` (hull) and q-pilot region (III:10841-10843);
- D22: `R_{≤−|log Θ|} ⊆ R` and `−|log q|∈R` (III:10845-10850);
- D23: global arithmetic degrees = log-volumes (III:10851-10855).

## 2. Our rank-one determinant layer

`tmp/sheaf/xif/paper/DeterminantLogVolumeActual.lean`:
- `LineBundle k := FractionalIdeal (nonZeroDivisors O_k) k`;
- `determinantLine I := I`;
- `determinantNorm I := FractionalIdeal.absNorm I`;
- `determinantNorm_mul`, `determinantNorm_nonneg`;
- `globalLogVolume I := Real.log (determinantNorm I : Real)`;
- `globalLogVolume_mul` (additive on nonzero bundles);
- `localizedLine I v : Submodule (O_v) (K_v)`;
- `localizedLine_mono` (monotone in I);
- `localLogVolume`, `sectionLocalLogVolume`, `sectionLogVolume`;
- `PaperDeterminantLogVolumeData` with fields `lineBundle`, `determinantLine`,
  `determinantNorm`, `globalLogVolume`, `localRing`, `localField`,
  `localizedLine`, `localValuation`;
- `actualDeterminantLogVolumeData I`.

Limitations:
- determinant is **rank-one only**: `determinantLine I = I`;
- no rank>1 vector bundle, no top exterior power, no tensor powers of a determinant;
- localizations are `Submodule O_v K_v`, not a determinant line of a rank>1 local
  system;
- no region inclusion / log-volume comparison API here.

## 3. S2807 `hpacket` assumption

`S2807SG3bScalarActual.lean`:
```lean
theorem S2807_upperGap_of_packetLogVolume_le
    (logQ dmod dFpd fFpd eStar etaPrm packetLogVolume : Real)
    (hpacket : actualC3LogShellTensorLogVolume (S2717C3 ...) = packetLogVolume)
    (hscalar : -packetLogVolume ≤ CThetaPaper ... * paperQAbsLog fiveLabel logQ) :
    S2717UpperGap ... := ...
```
So the determinant comparison is not proved; it is the explicit `hpacket`
identity between the actual tensor Haar log-volume and an abstract packet volume.
The scalar `hscalar` is likewise an explicit hypothesis.

`S2807ThetaHullVolumeIdentityActual.lean` gives:
```lean
S2807_thetaHullVolume_eq_haarRegion :
  S2717ThetaHullLogVolume ... =
    - (haarLogVolume (actualC3LogShellTensorHaar ...)
        (actualC3LogShellTensorRegion ...)).toReal
```
and `S2807_paperCor312Full_iff_haarRegion` rewrites the paper target in terms of
the actual Haar log-volume of the C3 log-shell tensor region.

## 4. What rank>1 determinant formalization needs

To state paper xi-d literally (rank>1 localizations, positive tensor power of det):

1. **Finite-free local lattice**
   `L_v : Submodule O_v (TensorBlock)` with `Module.Free O_v L_v`,
   `Module.Finite O_v L_v` (or a finite free `O_v`-module plus inclusion).
   Existing infrastructure: `FinitePadicIntegralLattice`, `FinitePadicSubmoduleTensor`,
   `tensorIntegralRegion`, `C3LogShellTensorBlock` (actual tensor block).
2. **Top exterior power / determinant module**
   `detModule L_v := ⋀^n L_v` (Mathlib `exteriorPower`), with `n = finrank`;
   prove it is free rank one; identify with an `O_v`-lattice.
3. **Determinant line bundle and norm**
   a rank-one `LineBundle`/`Submodule` for `det`; a norm/index
   `detNorm : ℚ` (or `ℝ`) using the lattice index;
   `detNorm_mul`, `detNorm_tensorPower` (`det(L^{⊗k}) = det(L)^{⊗k}`).
4. **Tensor powers**
   `L_v^{⊗k}` for the positive power `k` in paper xi-d; norm is `detNorm^k`.
5. **Localization/region comparison**
   the theta-hull region and q-pilot region as subsets of the same tensor block;
   **correct direction** `thetaHullRegion ⊆ qPilotRegion`; monotonicity of Haar log-volume.
6. **Log-volume normalization**
   `haarLogVolume` is `ENNReal`, so the real comparison needs finite/nonzero
   hypotheses and `ENNReal.toReal` monotonicity; a new lemma
   `haarLogVolume_mono_of_subset` is needed.

Cost estimate: steps 1-4 are a medium-size new module (exterior powers + lattice
index/norm + tensor powers); step 5 is a source identification (hard); step 6 is
a local measure lemma (easy).

## 5. Minimal formalizable subgoal (recommended)

Avoid rank>1 determinant by using the rank-one q-pilot line bundle and a direct
region inclusion:

**Subgoal A (rank-one determinant side).**
Use existing
`LineBundle`, `determinantLine`, `determinantNorm`, `globalLogVolume`,
`localizedLine`, `localizedLine_mono`.
Goal:
`globalLogVolume(qPilotLineBundle) = -|log q|` (or the corresponding signed
normalization).  This only needs the q-pilot fractional ideal and the existing
norm/log-volume lemmas.

**Subgoal B (region inclusion).**
Define/identify
`qPilotRegion : Set (C3LogShellTensorBlock)` and
`thetaHullRegion := actualC3LogShellTensorRegion`,
and prove **`thetaHullRegion ⊆ qPilotRegion`** (correct direction; the opposite gives the
reversed inequality).
This is the rank-one shadow of the paper's determinant comparison; the paper uses
`det` only to reduce rank>1 localizations to a line bundle.  It bypasses the
rank>1 exterior-power construction.

**Subgoal C (Haar monotonicity).**
Already green: `haarLogVolume_mono`
(`LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceIQHullInterface.lean:68`)
proves `S ⊆ T → haarLogVolume μ S ≤ haarLogVolume μ T`, with no finiteness hypothesis
(the `⊤` case is handled separately).  For the signed comparison use
`logVol S := -haarLogVolume μ S`; then `S ⊆ T ⇒ logVol T ≤ logVol S`.
`Mzk1QRegionInclusionActual.haarLogVolume_mono_of_subset` is the same statement
for the negative-log-volume structure `RegionLogVol`.

**Subgoal D (paper inequality from A-C).**
From **`thetaHullRegion ⊆ qPilotRegion`** and C, with `logVol S := -log μ(S)`:
`logVol(qPilotRegion) ≤ logVol(thetaHullRegion)` (the larger set has smaller negative-log volume);
with `logVol(qPilotRegion) = -|log q| = -A` and
`logVol(thetaHullRegion) = -|log Θ| = -R`, this yields `-A ≤ -R`, i.e.
`−|log Θ| ≥ −|log q|` (`C_Θ ≥ −1`) once the `C_Θ` upper bound is supplied.

## 6. Rank>1 vs rank-one decision

- **Rank-one minimal**: Subgoals A-D use only existing rank-one
  `DeterminantLogVolumeActual` plus a new monotonicity lemma and a source region
  inclusion.  This is the shortest path to a paper-shaped xi-d comparison.
- **Rank>1 literal**: needs exterior powers, lattice determinant norms, tensor
  powers, and a region comparison at the vector-bundle level; larger and not
  currently present.  It should be a separate port if the paper's exact
  `det(localizations)^{⊗k}` object is required.
- Recommendation: state the rank>1 determinant comparison as an explicit
  interface/hypothesis (as `hpacket` already does) and formalize Subgoals B-D;
  do not pretend the rank>1 det is constructed.

## 7. Missing declarations checklist

Rank-one minimal:
- `qPilotLineBundle : LineBundle` (source q-pilot divisor);
- `thetaHullRegion : Set (C3LogShellTensorBlock)` and `qPilotRegion` with their log-volume identifications;
- `haarLogVolume_mono` (already green; `Mzk1QRegionInclusionActual` has the negative-log form);
- `thetaHullRegion_subset_qPilotRegion` (source GAP; correct direction A1049);
- `globalLogVolume_qPilot_eq_neg_absLog` (q-pilot identification GAP).

Rank>1 literal:
- `LocalizedVectorBundle` / finite free lattice;
- `detModule` (top exterior power);
- `detNorm` (lattice index/norm);
- `detTensorPower` and norm power law;
- `localizedDet` and determinant comparison;
- region inclusion and normalization.

---

## 8. Direction correction (A1049)

> The correct sufficient inclusion is **`thetaHullRegion ⊆ qPilotRegion`**.
> With `logVol S := -log μ(S)`, monotonicity gives
> `logVol(qPilotRegion) ≤ logVol(thetaHullRegion)`, i.e. `-A ≤ -R`;
> the opposite inclusion `qPilotRegion ⊆ thetaHullRegion` gives `-A ≥ -R`, which is the
> wrong direction for Cor 3.12.  Accordingly, Subgoal B and the missing-declaration name
> are `thetaHullRegion_subset_qPilotRegion`; `Mzk1QRegionInclusionActual`
> (`variant_rankone_conditional`) records this already.
>
> **A1050 confirmation**：`logVol=-log μ`，`-A=-|log q|`、`-R=-|log Θ|`；variant `-A≤-R ⇔ A≥R`；
> `A=log μ(q)`、`R=log μ(theta)`，log 严格单调 ⇒ `A≥R ⇔ μ(q)≥μ(theta)`；measure 单调只给**单向**
> `thetaRegion⊆qRegion ⇒ μ(theta)≤μ(q)`，故 `thetaRegion⊆qRegion` 是**充分条件，不是等价**。
> A1048b 的 `q⊆θ` 说法**作废**；反向只给 `-A≥-R`。
