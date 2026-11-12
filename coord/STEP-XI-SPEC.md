# STEP XI SPEC — checkable inference-chain draft

Status: 2026-11-11 (A799/A801). Sources: lana full Iut tree at D:\lean\Iut (694 files, 0 sorry,
0 axiom); this repo source inputs: `SourceLinkFactorization`, `kummerMap_thetaOne`,
`SourceAPTStatement`, `SourceLocalizationExpressible`.

Step (xi) is the contested step of IUT III Cor. 3.12. We decompose it into minimal
propositions (P1–P8). Each row gives: statement, green theorem (file:line) or PENDING.
Honesty: no row marked PENDING is claimed proved; the final ABC input remains open.

## Minimal propositions

### P1 — Θ-link is a value-group poly-isomorphism whose unit part is the F^⊢×μ link
Statement: for theaters H1 H2 of D, ThetaLinkIso D H1 H2 := (gauStrip D H1).Iso (qStrip D H2),
unitEquiv identifies it with H1.Fmu.Iso H2.Fmu, and dLink is the F^⊢×μ link.
Green: Iut/ThetaLink/Link.lean:72 (abbrev ThetaLinkIso), :90 (unitEquiv), :140 (dLink).

### P2 — Θ-link rescales value-group degrees by 1/s, and does not preserve degrees
Statement: val_apply rescales the degree coordinate by 1/s; s ≠ 1 so no Θ-link is
degree-preserving; pilot degrees are s·|log q| (Θ-side) and |log q| (q-side).
Green: Iut/ThetaLink/Link.lean:109 (val_apply), :129 (val_not_degree_preserving),
:120 (pilot_degrees); Iut/ThetaLink/Gauss.lean:228 (avgDeg_gaussian, degree is s·deg q).

### P3 — Θ-link does not exist in the realified global Frobenioid; only R_{>0}-scalings do
Statement: thetaPilotObj and qPilotObj are not isomorphic; exactly the scaling 1/s carries
one to the other; the oriented lattice graph has only translations (no adjacent swap).
Green: Iut/ThetaLink/Link.lean:200 (not_iso_in_frobenioid), :206 (scaling_iff),
:227 (arrow_aut_eq_add), :237 (not_swap_adjacent).

### P4 — transport law: logVol(LGP·S) = −s·|log q| + logVol(S) on (Ind3)-choices
Statement: the identified-copies output law along horizontal and vertical arrows; the
distortion of the transport is zero; Kummer identifications preserve log-volume.
Green: Iut/LogLink/Thm311.lean:256 (logVol_transport_out), :267 (answer);
Iut/ThetaLink/Wall.lean:228 (distortion_eq_zero), :220 (kummerVolCompat), :223 (volCompat).

### P5 — (Ind3) log-volumes fill (−∞, V], V = log-vol(hull(VC(I)))
Statement: for every t ≤ V there is an (Ind3)-choice of log-volume t; the hull/container
payload is the least hull of the log-shell container.
Green: Iut/WallEquiv/Basic.lean and Iut/Wall/Ind3.lean (exists_ind3_logVol_iff);
Iut/WallEquiv/Gap.lean:87 (leastHull), :107 (exists_leastHull_eq),
:123 (leastHull_admissible), :919 (gapHullAt_eq).

### P6 — Step (xi) minimal inequality: (s−1)·|log q| ≤ log-vol(hull(VC(I)))
Statement (XiPrinciple, in lattice model): outputs transported along each horizontal arrow
compute the q-pilot up to indeterminacies, i.e. K.model.WallOn horizRel.
Green: Iut/LogLink/Thm311.lean:203 (def XiPrinciple), :219 (xi_iff_ss: exactly
(s−1)·|log q| ≤ log-vol(hull(VC(I)))); def SSIneq Iut/Wall/MultiContainer.lean:88.
Status: PENDING (the real Step (xi); open ABC-strength input).

### P7 — averaged (sFactor−1) coefficient and cancellation of the difference terms
Statement: averaging over the procession of capsules gives the coefficient
(sFactor−1)/(2ℓ) in the ABC normalized form; the different/shell-defect terms cancel the
packet index term up to the log-lattice slack; at tame primes the defect equals the packet
index term exactly.
Green: Iut/WallEquiv/VcI.lean:414 (shellExcess_eq_tame), :435
(componentVol_leastHull_tensorLogShell_eq_tame), :450 (shellDefect_eq_neg_orderVol_tame),
:870 (defectPacket_tame_le), :844 (hullPacket_tame), :316 (abs_shellDefect_add_orderVol_le);
A763 math calibration: c_V = 1/4, Szpiro constant 6 (zero slack).
Status: the (2ℓ) normalization is a bookkeeping fact on (sFactor−1) = 2ℓ·c_V-like formulas;
the informal derivation is A763, the exact Lean identity between sFactor and c_V · 2ℓ is
PENDING (it is not stated as a theorem in lana or here).

### P8 — gap decomposition: SS vs the Cor. 3.12 variant
Statement: gap Δ(D) = rhs − log-vol(LGP·hull(VC(I))) ≥ 0; SS ⇔ variant with rhs lowered
by Δ; Δ = 0 iff the (Ind2)-terms vanish at all bad residue characteristics; the no-hull
gap Δ_noHull > 0 strictly, so the no-hull wall is strictly stronger.
Green: Iut/WallEquiv/Gap.lean:505 (gap), :512 (gap_nonneg), :543 (variant_of_ss_gap),
:548 (ss_iff_variant_of_gap_eq_zero), :959 (gap_eq), :871 (gapNoHull_pos),
:986 (ss_iff_variant_of_ind2Term).
Status: P8 is PROVED except the converse Δ=0 case which is conditional (as stated).

## Inference chain (end-to-end)

P1–P3 (value-group/degree layer) → P4 (transport law) → P5 (Ind3 volume range) →
P6 (Step xi: SS inequality) → P8 (SS ⇔ variant, up to Δ) →
Iut/Wall/EtaAlg.lean:201 (variant_of_wall) → Iut/MainTheorem.lean:39
(classicalABC_of_variant) → Iut/Abc/Classical.lean ClassicalABC →
our Mzk1FinalABCBridgeActual (classicalABC_implies_ABCConjecture).
Green assembly already machine-checked in lana: xi_iff_ss (Thm311.lean:219),
classicalABC_of_xi (Thm311.lean:241), Wall.classicalABC_of_wall (EtaAlg.lean:223).

## What is missing (gaps)

G1 Step (xi)/SS itself (P6) = open Szpiro-6 (A763). Only hypothesis, never assumed.
G2 Thm 3.11 does not imply Step (xi) (NonDerivable.lean): xi_iff (:273),
   not_xi_family (:475), exists_package_not_xi (:491), not_forall_xi (:543);
   the package-faithfulness statement is audited, not a theorem (module docstring).
G3 Two unproved volume Props (VcI.lean): ShellExcessAdditive (:631),
   PacketIndexFormulaGalois (:640) — finite-dimensional determinant computations.
G4 Cross-repo dictionary: SSIneq vs our corrected-region BadSumWeightBound
   (Mzk1CorrectedGap2ToABCActual / Mzk1FinalBoundaryCertificateV2Actual): no Lean bridge yet.
G5 Transport into our tree: Mzk1FinalABCBridgeActual is written but pending the full Iut
   compile (Cor312/Statement → Concrete/ThetaRegion → Wall → MainTheorem).

## Immediate Lean formalization target

A first formalizable statement (no open input, pure dictionary):

def StepXIMinimalStatement (D : Iut.InitialThetaData.{0}) : Prop :=
  Iut.Wall.SSIneq D

theorem stepXIMinimal_iff (D : Iut.InitialThetaData.{0}) :
    StepXIMinimalStatement D ↔ (sFactor (nC D) - 1) * D.qPilot.absLogQ ≤ logVol D (hullOf D (vcI D)) := Iff.rfl

and the proved implications: SSIneq → Corollary312Variant (Gap.lean:543, conditional on
the gap being zero — so the unconditional version stays PENDING), xi_iff_ss (Thm311.lean:219).

A lana-free compilable variant is provided by shehdd:
`tmp/sheaf/xif/paper/Mzk1StepXIMinimalStatementShaActual.lean` (EXIT=0, olean=True,
gates trio): `StepXIMinimalStatement := SSIneqExplicit`, and
`stepXIMinimal_iff_lanaShape : logq = 2l*A -> ((sC-1)*(logq/2l) <= V <-> (sC-1)*A <= V)`.

## Coordination

* mainline: lana compile/DAG, graph import-parser fix A783, this spec.
* shehdd: paper-faithful 3.12 normed (Mzk1PaperFaithful312NormedActual) and hqneg.
* stepxi: assembly consumer Mzk1StepXICor312FullAssemblyActual / Mzk1Cor312FullActual.
* qpilot/stage4: vendor tree closure (Iut, CurvesJacobian, WeilCurves, Belyi).

This is a living draft: append findings and change statuses (PENDING → PROVED) with file:line evidence.

## 6. This repo's interface mapping (P1–P8) — added A801

Our own Step-XI surface (all green, but not yet related by Lean to lana's SSIneq):

| our object | file:line | corresponds to |
|---|---|---|
| `SourceLinkFactorization` (IPL frozen formula: lower horizontals + kummer + evaluation, factorization equality) | `LeanFormal/IUT/IUTIII/Theorem311/SourceKummerEvaluationArrows.lean:418` | P1/P4 (Θ-link transport law; the paper's IPL composite) |
| `kummerMap_thetaOne` (Kummer realization of the theta-pilot; `Mzk1KummerTransportActual`) | `tmp/sheaf/xif/paper/Mzk1KummerTransportActual.lean` | P4/P5 (Kummer identifications, theta value realization) |
| `SourceAPTStatement` (nonempty algorithmic parallel transport) | `LeanFormal/IUT/IUTIII/Corollary312/StepXI/APT.lean:308` | P5/P7 (transport of outputs/indeterminacies) |
| `SourceLocalizationExpressible` (localization expression at each place) | `LeanFormal/IUT/IUTIII/Theorem311/SourceArithmeticHolomorphicLanding.lean:292` | P5/P8 (landing of outputs; volume comparison) |

Mapping status: the four objects above are the source-level obligations used by stepxi's
three-card contract (`StepXIContract` IPL/SHE/APT slots), and they are not yet connected
to lana's `SSIneq`/`Wall`/`XiPrinciple` definitions. That cross-repo dictionary is gap G4.

Minimum Lean target (see file `tmp/sheaf/xif/paper/Mzk1StepXIMinimalStatementActual.lean`):

    def StepXIMinimalStatement (D : InitialThetaData.{0}) : Prop := Wall.SSIneq D
    theorem stepXIMinimal_iff (D) : StepXIMinimalStatement D ↔
      (sFactor (nC D) - 1) * D.qPilot.absLogQ ≤ logVol D (hullOf D (vcI D)) := Iff.rfl

`stepXIMinimal_iff` is a pure unfolding (will compile once the lana oleans exist); the
open content is P6, i.e. inhabiting `StepXIMinimalStatement`, and is out of scope here.

---

## 7. shehdd review + paper-faithful appendix (A801/A802)

### 7.1 paper-faithful normalized 3.12 (hqneg)
* `Mzk1PaperFaithful312NormedActual` (green, olean): `rpVolumeNorm S = rawHaar S / rawHaar fullRegion`,
  `rpRequirementNorm`, **`hqneg_norm` unconditional**, `final_3_12_normed` (only IPL/SHE/APT evidence params).
* reduction: `hqneg_iff_rpVolume_lt_one` (`Mzk1PaperFaithful312HqnegActual`):
  `requirementSignedQ (rpRequirement T) < 0 ↔ rpVolume T (rpRegion T) < 1`.
* normalization dictionary: the S1902 normalized log (relative to the product unit ball) is
  `rootExtensionProductNormalizedLog`; it does **not** include the S1902 `+1`, so
  `rootExtensionProductNormalizedLog (scaledThetaHull k) = scaledClosedFormR k − 1`
  (green: `Mzk1ScaledThetaHullNormalizedLogShaActual`, gates trio).
* scaled closed form: `s1915ClosedForm = 1 + Σ_b d_b log rootImageRadius_b`,
  `scaledClosedFormR k = s1915ClosedForm − k·Σ_b d_b log p_b` (green A775-1 file
  `Mzk1ScaledThetaHullScalingShaActual`: `scaledThetaHull_measure_eq` / `scaledThetaHull_log_toReal`).

### 7.2 `rpRequirementNorm` ↔ lana `sFactor/ℓ` (expected dictionary, G4 input)
lana: `SSIneq D := (sFactor (nC D) - 1) * D.qPilot.absLogQ ≤ logVol D (hullOf D (vcI D))`
(`Iut/Wall/MultiContainer.lean:88`).
ours: `SSIneqExplicit sC logq l V := (sC - 1) * (logq / (2*l)) ≤ V`
(`Mzk1SSIneqExplicitFormActual`), and `Mzk1KappaLemmaActual.sL l = l(l+1)/12`.

Expected dictionary fields (TODO, no Lean bridge yet):
1. `sC = sFactor (nC D)`;
2. `logq = 2*l*|log q| = 2*l*A` (lana `absLogQ`);
3. `V = logVol D (hullOf D (vcI D))` (the corrected/normalized hull log-volume).
Under these fields the two inequalities are algebraically the same.  The lana half is green;
our half is green; the dictionary itself is G4.

Our contribution to the sFactor side (green):
* per-capsule sum: `Σ_{j<n} ((j+1)^2 − 1) = n·(sFactor n − 1)`
  (`Mzk1ShellArithmeticIdentitiesActual.shell_sum_identity`);
* procession average of the scaled closed form:
  `avg_{i<n} scaledClosedFormR((i+1)^2/(2ℓ)) = s1915ClosedForm − sFactorFin(n)·S`
  (`Mzk1ScaledThetaHullShaActual.processionAverage_scaledClosedForm`);
* capsule exponent correspondence: paper `qroot^{j²}` gives divisor exponent
  `k_b = c_norm_b·j²/(2ℓ)`; integer `k` matches exactly iff `k = k_b` for all b
  (`Mzk1ScaledThetaHullScalingShaActual.scaledHullRadius_eq_capsuleHullRadius_of_cast`).

### 7.3 P1–P8 completeness review
Covered: Θ-link structure/degree (P1–P3), transport law (P4), Ind3 volume range + hull (P5),
Step (xi) = SSIneq (P6, open), sFactor/procession (P7), gap/variant (P8).
Missing / should be added:
* **P9 (archimedean)**: lana log-volume includes archimedean `log(√2·π)` defects
  (`Iut/WallEquiv/VcI.lean:657,700`); our S1902 product log has no archimedean factor.
  PENDING in our tree; needed for exact `logVol` dictionary.
* **P10 (label reading / procession switch)**: lana uses uniform procession average
  (`ArchScaling.lean:485–498`) and labels `ivLabels={distinguished}` vs `litLabels=univ`;
  our `Mzk1SwitchAuditActual` records both switches; the max-vs-average and label choices
  must be fixed in the dictionary.
* **P11 (unit normalization)**: q-pilot `-|log q|` vs `rootExtensionProductNormalizedLog`
  differs by the S1902 `+1` unit term; already corrected in `Mzk1ScaledThetaHullNormalizedLogShaActual`.
* **P12 (retraction guard)**: `final_conditional_ABC.hfull` is RETRACTED (unsatisfiable for
  fixed T, A703); any spec step must not use it.  `Mzk1RetiredBoundaryAuditActual` is the
  canonical record.

### 7.4 G4 expected statement (TODO, to be proved)
```lean
-- expected shape (NOT proved; needs lana olean + archimedean/procession dictionary)
structure StepXISSIneqDictionary (D) where
  sC_eq : sC = sFactor (nC D)
  logq_eq : logq = 2 * l * D.qPilot.absLogQ
  V_eq : V = logVol D (hullOf D (vcI D))

theorem SSIneq_iff_explicit (D) (Dict : StepXISSIneqDictionary D) :
  Wall.SSIneq D ↔ SSIneqExplicit Dict.sC Dict.logq Dict.l Dict.V
```
The arithmetic identity under the dictionary is pure `ring`; the missing content is the
dictionary (G4) + archimedean/procession (P9/P10).  Until then G4 stays **PENDING**.

## 8. G4 verdict (A802, with audit file)

`SSIneq D ↔ BadSumWeightBound T eN` is NOT available as a clean dictionary; audit file
`tmp/sheaf/xif/paper/Mzk1G4DictionaryAuditActual.lean` (EXIT=0 + olean, 10 rows, clean gate)
records the three obstacles:

* O1 quantifier shape: one fixed inequality (SSIneq) vs a uniform ε-family over all triples
  (BadSumWeightBound); needs an explicit normalization theorem, absent in both repos.
* O2 data mismatch: no Lean map lana `InitialThetaData` ↔ our `SourceNativeInitialThetaData`;
  lana LHS is a single scalar `(sFactor−1)·absLogQ`, ours is a finite sum over bad primes
  `Σ_b eN_b·d_b·log p_b`. Needed: data map, sFactor/coefficient identity, per-prime expansion.
* O3 `hfull` for fixed T is UNSATISFIABLE (`Mzk1FinalConditionalVacuityActual.hfull_unsatisfiable`),
  so `badSumWeightBound_implies_ABC` is vacuous as stated (A703 retraction).

Per-N construction: choosing bad support = primeFactors N and eN = v_p(N) satisfies `hfull`
by unique factorization; then (with d_b = 1) bad sum = log N, and BadSumWeightBound becomes
`log N ≤ (1+ε)·log rad(abc) + D` for N = 2c+1 — i.e. ABC up to log 3
(`logN_le_log_c_add_log3`). So the non-vacuous version of the corrected-region chain is a
restatement of ABC, not a corollary of lana's `SSIneq`. Consequently closing G4 requires the
two normalization/expansion bridges above, not only definitions.

### 7.5 A801/A804 follow-up: P7 Lean status, P9/P10 evidence, G4 skeleton (shehdd)

**P7 Lean status (new, green):** `tmp/sheaf/xif/paper/Mzk1StepXIP7IdentityShaActual.lean`
(EXIT=0, olean=True, gates trio):
* `p7_coefficient_identity`: `(sFactor n-1)*(logq/(2l)) = ((sFactor n-1)/(2l))*logq`;
* `p7_capsule_average`: `(1/n)Σ_{j<n}((j+1)^2-1) = sFactor n-1` (green `shell_average_identity`);
* `p7_scaled_procession`: `avg_i scaledClosedFormR((i+1)^2) = s1915ClosedForm - sFactorFin(n)*S`;
* `p7_ssIneq_explicit_coefficient`: `SSIneqExplicit (sFactor n) logq l V ↔ ((sFactor n-1)/(2l))*logq ≤ V`.
Still PENDING for P7: the exact lana calibration `sFactor(nC) ↔ 2ℓ·c_V` (c_V = 1/4, Szpiro 6);
the spec statement stays honest.

**P9 (archimedean) — PENDING, no green in our tree.**  lana has the archimedean defects at
`Iut/WallEquiv/VcI.lean:657,700`; our dictionary file records the gap at
`tmp/sheaf/xif/paper/Mzk1LogVolumeDictionaryActual.lean:17-18` (archimedean contribution is
`log(√2·π)`-type, missing from our S1902 ball log).  Needs a real construction, not assumed.

**P10 (label/procession switch) — partly GREEN.**  `tmp/sheaf/xif/paper/Mzk1SwitchAuditActual.lean`:
* `paperScaleExponent_label_indep` (:77), `paperScaleExponent_eq` (:81) — theta exponent `(i+1)^2`
  fixed per capsule, label only selects the tensor factor;
* `processionAvg_le_max` (:94) and `max_rhs_not_faithful` (:113) — uniform average vs maximum
  is a real switch (max makes the wall easier);
* `ivReading_subset_literalReading` (:127) — labels reading choice documented.
Still PENDING: binding our `scaledClosedFormR`/`sFactorFin` to lana's `nC`-indexed procession.

**G4 dictionary skeleton (new, green):** `tmp/sheaf/xif/paper/Mzk1StepXISSIneqDictionaryShaActual.lean`
(EXIT=0, olean=True, gates trio): `structure StepXISSIneqDictionary` with fields
`sC, logq, l, A, V, lanaLogVol, nC, sC_eq : sC = sFactor nC, logq_eq : logq = 2*l*A,
V_eq : V = lanaLogVol, hl : l != 0`; and
`SSIneqExplicit_iff_lanaShape : SSIneqExplicit sC logq l V ↔ (sC-1)*A ≤ lanaLogVol`
(plus the `sFactor nC`-exposed form).  §7.4 keeps **PENDING** for the lana instantiation.

### 7.6 A805 paper-side `r` definition check (shehdd)

lana/paper `r`: at a finite place the log-shell radius `r_w` is defined by
`logShellRadius w p := sSup ((fun y => -ordp K w y) '' (logShell ... \ {0}))`
(`Iut/WallEquiv/VcI.lean:463`), achieved at the maximizing element (:468, :471), and the
sharp radius law is `I_w <= p^{-r_w} O_w`.

Our completed-root side: **`paperR_b := c_norm_b/(2ℓ)`**, and
`tmp/sheaf/xif/paper/Mzk1PaperRDefinitionAuditShaActual.lean` (EXIT=0, olean=True, gates trio) proves
* `rootImageRadius_eq_rpow_neg_paperR`: `rootImageRadius_b = p_b^{-paperR_b}`;
* `log_rootImageRadius_eq_neg_paperR_mul_logp`: `log rootImageRadius_b = -paperR_b·log p_b`;
* `capsuleDivisorExponent_eq_paperR_mul`: A775 capsule divisor exponent `= paperR_b·j²`
  (so paper scaling `qroot^{j²}`, `j=i+1`, has exact divisor `paperR_b·j²`);
* `qroot^{2ℓ}=qUnit` side is green `rootNormedElement_pow` (`PaperRootCompletionTensorActual`).

**PENDING (lana olean)**: exact equality `paperR_b = logShellRadius` at the finite place
(`VcI.lean:463/468/471`); recorded, not asserted (no lana import here).

### 7.7 A806 Szpiro upper-bound shape (shehdd)

`tmp/sheaf/xif/paper/Mzk1SzpiroUpperBoundShapeShaActual.lean` (EXIT=0, olean=True, gates trio):
* `SzpiroUpperBound C := ∀ a b c, IsABCTriple a b c →
   Real.log c ≤ 6·Real.log(radical(a*b*c)) + C` (constant `C` explicit);
* `szpiroUpperBound_iff_epsilon`: equivalent `(1/6)·log c ≤ log rad + C/6`;
* `szpiroUpperBound_iff_forall_shape`: per triple `Szpiro6Shape (log c) (log rad) C`
  (`Mzk1FinalBoundarySzpiroActual.Szpiro6Shape` has signature `logq logdf C`);
* `szpiro6Shape_iff_sixth_triple` re-export.
PENDING: the bound itself (open ABC-strength) and the exact `ABCConjecture ↔ SzpiroUpperBound`
log-form estimate (paper arithmetic; not formalized here).  No claim is made that the bound holds.

### 7.8 A811 volume identification audit (shehdd)

`tmp/sheaf/xif/paper/Mzk1VolumeIdentificationAuditShaActual.lean` (EXIT=0, olean=True, gates trio):
* raw scaling `volume_raw_scaling`; raw log `volume_raw_log_scaling`;
* normalized `volume_normalized_scaling` = `scaledClosedFormR k - 1` (S1902 +1 corrected);
* `volume_full_eq_s1915`: `s1902LogVolume fullRegion = ofReal(s1915ClosedForm)`;
* q side `volume_qSide_identification` / `volume_qReading_log_norm`;
* `volume_VPaper_closed_form`: `VPaper = scaledClosedFormR k - 1 + qSideContribution`;
* `volume_scaledStatement_iff`: statement ↔ `qSide >= 1 - scaledClosedFormR k`.

OPEN (pointer for `Mzk1FinalBoundaryCertificateV3Actual`): lana `logVol` bridge
(`Iut/Wall/Rss.lean:323-324` procession average `1/nC`; `Iut/WallEquiv/VcI.lean:740+` hull packet;
archimedean `VcI.lean:657,700`) and c_lana = `(sFactor-1)/(2ℓ)` with A763 c_V bookkeeping.  Not assumed.

### 7.9 A812 box assembly + A763 bookkeeping (shehdd)

`tmp/sheaf/xif/paper/Mzk1A763BoxAssemblyShaActual.lean` (EXIT=0, olean=True, gates trio):
* `sum_sq_range`: `Σ_{j<n}(j+1)^2 = n(n+1)(2n+1)/6`;
* **`sFactor_eq_sL`: `sFactor n = sL (2n+1)`** — the P7 exact calibration (lana capsule
  coefficient equals the paper hull coefficient `sL l = l(l+1)/12` at `l = 2nC+1`;
  `sFactor` from `Iut/Wall` procession, `sL` from `Mzk1KappaLemmaActual`);
* A763 constants re-exported: `cVModel = 1/4`, `szpiroThreshold cVModel = 6`;
* **`a763_box_szpiro`**: `SSIneqExplicit (sFactor nC) logq l V` + hull upper bound
  `V ≤ (1/4)·l·logdf + C0` (+ `l ≥ 12`, `C0 ≥ 0`, `logdf ≥ 0`) ⇒
  `Szpiro6Shape logq logdf (2*C0)` (using hull's `ssIneqExplicit_to_szpiro6`).

Still PENDING: the hull upper bound `V ≤ (1/4)l·logdf + C0` itself (hull `Mzk1VolumeUpperActual`
/ `Mzk1SzpiroUpperABActual` open item) and the geometric identification of `logVol` with
`l·logdf` (archimedean/procession/c_lana, §7.8).  No fake bound, no RETRACTED use.

### 7.10 A812/A822 box-coefficient identification (shehdd)

`tmp/sheaf/xif/paper/Mzk1BoxCoeffIdentificationShaActual.lean` (EXIT=0, olean=True, gates trio):
* `box_cForm_eq_sL`: hull's box coefficient `cForm l = (l+1)/24 - 1/(2l)` equals
  `(sL l - 1)/(2ℓ)` (A763/P7 bookkeeping);
* `box_ssIneqCoeff_eq_cForm`: the boundary file's SSIneq coefficient is `cForm l`;
* `box_cForm_eq_sFactor`: at `l = 2nC+1`, `cForm l = (sFactor nC - 1)/(2ℓ)` — the lana
  capsule coefficient and the hull box coefficient coincide exactly.

Status of hull/mainline box closure files (compiled here, all green):
`Mzk1StepVIdentificationActual` (gates trio; object identification `V = stepVExpr` is an
explicit hypothesis), `Mzk1PaperStepVBoxActual` (paper Step-V inequality proved; no absolute
constant), `Mzk1SzpiroFromBoxActual` (honest `(1+eps(l))` form, plain 6 NOT claimed),
`Mzk1VolumeIdentificationActual` (tame identification + conditional general identification).

Remaining geometric box gap (unchanged): `V <= ((l+5)/4)·logdf + C0` and its `(1/4)l`
normalization; object dictionary `V = stepVExpr` / lana `logVol`.  Coefficients are now
proved identical across all three languages (sL / sFactor / cForm).

### 7.11 A825 box/volume closure status (shehdd compile check)

Latest hull files compiled here, all green (EXIT=0, olean=True, gates trio):
* `Mzk1VolumeUpperLeActual` (A825): changes the object dictionary from equality to
  inequality `V ≤ stepVExpr`; proves the per-place assembly
  `-λ + Σρ ≤ -floor(λ-dI-aI)+bI` and its `·log p` version, plus
  `volume_upper_of_le_dictionary`;
* `Mzk1StepVIdentificationActual` (updated): conditional `StepVDictionary ⇒ V ≤ paperBox`,
  `PaperDictionaryShape`; object identification `V = stepVExpr` remains GAP.

Remaining real inputs (unchanged):
1. per-place lana instances `ρ_w ≤ b_w + 1 + [p=2]`, `d_w + a_w ≥ 1 + [p=2]` and the
   global sums on the lana hull(vcI) carrier;
2. object/carrier identification between our S1902/C3 paper-normalized volumes and
   lana's `stepVExpr`/`logVol` (archimedean + procession + `λ/different` bookkeeping).

Coefficient layer is already unified by §7.10 (`cForm = (sL-1)/(2ℓ) = (sFactor-1)/(2ℓ)`);
the remaining gap is geometric/object-level, not bookkeeping.

### 7.12 A832 Step-(xi) formalization attempt: the exact missing proposition (shehdd)

`tmp/sheaf/xif/paper/Mzk1StepXIFormalizationAttemptActual.lean` (EXIT=0, olean=True, gates trio).

Formalized abstract chain (lana P1–P5 as inputs, no lana import):
* data `ThetaLinkVolumeData (A V s κ)` with P4 `κ = -(s*A)` (lana `ThetaShift`,
  `MultiContainer.lean:104-107`; `logVol_transport_out`, `Thm311.lean:255-262`);
* P5: Ind3 log-volumes are exactly `(-inf, V]` (`exists_ind3_logVol_iff`, `Wall/Ind3.lean:252`),
  hence every Ind3 `S` has `logVol S <= V`;
* `StepXIChoiceCondition A V κ := -A - κ <= V`;
* `ssIneq_of_choiceCondition`: P4 + choice condition ⇒ `(s-1)A <= V`;
* **`hull_not_lgp_output_of_ind3`**: `V = -sA + t` with `t <= V` is impossible for
  `A,s > 0` — so the naive step “take `S' = hull`” cannot produce the hull from an
  Ind3 region; the missing input is a choice/alignment, not a volume-range fact;
* **`P4_not_sufficient`**: explicit counterexample `A=1, V=0, s=2, κ=-2` satisfies P4
  but fails the choice condition.

**Exact missing proposition (lana `WallOn`/`XiPrinciple` in volume form):**
`StepXIAdditionalLemma A V κs := ∃ κ ∈ κs, -A - κ <= V`, i.e. there exists a choice
whose LGP/Θ-link shift satisfies `qPilot.lhs - κ <= V`.  Under P4 it is equivalent to
SSIneq; lana proves the equivalence with SSIneq (`xi_iff_ss`, `Thm311.lean:218`) and the
volume-form wall (`wall_iff_of_lgpLaw`, `Wall/Checks.lean:111-120`); `NonDerivable.lean`
shows P1–P5 do not imply it.  So the entire Step-(xi) lower-bound gap is this ONE
choice-existence proposition (not a volume-range or bookkeeping statement).

### 8.1 A832 refinement (shehdd): single choice-existence gap

`Mzk1StepXIFormalizationAttemptActual` (green, olean, gates trio) pins the Step (xi)
content to the single choice-existence proposition

    StepXIAdditionalLemma A V ks := exists k in ks, -A - k <= V

(the volume form of WallOn/XiPrinciple). With P4 (k = -s*A) it gives SSIneq; P4 alone
does not (counterexample A=1, V=0, s=2, k=-2); the hull is not an LGP output of Ind3
(`hull_not_lgp_output_of_ind3`, V = -sA+t with t <= V impossible for A,s>0). This agrees
with lana `xi_iff_ss` (Thm311.lean:219), `wall_iff_of_lgpLaw` (Wall/Checks.lean:111-120)
and `NonDerivable`. Consequence for G4: the dictionary target is this choice-existence
proposition (equivalently SSIneq), not `BadSumWeightBound`; see §7.10 (cForm coefficient)
and §8 (O1-O3).
