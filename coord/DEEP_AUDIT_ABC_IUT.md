# Independent deep audit — ABC/IUT formalization and paper route

Date: 2026-11-07. Auditor: transport (deep-auditor mode).
Scope: corrected A6 chain; IUT III source hull / theta upper / signed carrier;
S2935/S2941/S2945; mathematical audit of S2936 (read-only, no edits).

Method: full source reads of the named files, `.olean` presence, `#print axioms`,
and direct inspection of the IUT III/IV corpus text (`papers/motizuki_corpus/text/`).
No file was modified; S2936 was not edited.

## 0. Verdict summary

1. The corrected A6 chain is an ACTUAL CONDITIONAL ASSEMBLY, not a proof of
   corrected T from source data. It has no literal target-in-input circularity,
   but the hard geometric objects (Q/IsStack, quotient stack D, quotient witness,
   classification, groups, cusp, clauses) are all inputs.
2. The paper's IUT III Corollary 3.12 is NOT an ABC estimate. It is explicitly a
   **tautological computation**: Mochizuki says the construction yields 'two
   tautologically equivalent ways to compute the log-volume of the q-pilot object'
   (III:929, 1038, 10902); `C_Theta >= -1` follows formally (III:10897-10898).
   It is not circular in the narrow sense, but it is a structural identity, not an
   independent upper estimate. IUT IV Theorem 1.10 then computes C_Theta via
   explicit divisor/conductor bounds; no ABC hypothesis is inserted in Cor 3.12.
3. Our formal S2935/S2941/S2945 route does NOT reproduce Cor 3.12. It replaces the
   paper's tautological q-pilot computation by a **J-height <= procession average**
   inequality, an ABC-type height statement. S2945 merely defines the missing
   bridge Props; no equivalence is proved. This is gap relocation/strengthening,
   not the paper's step.
4. S2958 is an ACTUAL certificate but **tautological**: qSigned is chosen -1 and
   thetaSigned = hullVolume + 1 (or 0), with no actual q-pilot/C_Theta content.
   S2936/S2944 are algebraic constant absorptions, not theta upper certificates.
5. Raw source-hull upper route: the actual theorem
   `sourceThetaBound_unsat_of_degreeFaithful` is correct but conditional on
   pointwise degree faithfulness; it proves the value-realized hull is `top` under
   that hypothesis, so no real upper bound exists. It is not an absolute no-go
   unless degree faithfulness is forced for every admissible source realization.

## 1. Actual chain verification list

All listed declarations have axioms `[propext, Classical.choice, Quot.sound]`
unless noted. `.olean` SHA is the current file at audit time.

| artifact | source SHA | olean | axioms | status |
|---|---|---|---|---|
| S2905CoreWithHqW | 43F99929... | 38416 B BA087C9C... | trio | actual conditional core assembly |
| S2908CorrectedSActual | 7A51A2D1... | 68560 B F1236219... | trio | actual wrapper of S2905 |
| S2927CorrectedCompletionDownstreamActual | 861F05AB... | 68224 B 4D48E8D7... | trio | actual conditional completion |
| S2928CorrectedTConstructionActual | E360668D... | 141280 B 3D3C4B58... | trio | actual T from completion |
| S2934CorrectedTFromCompletionActual | 33C6BD7D... | 41888 B 866594A7... | trio | actual T identity/assembly |
| S2933PerTripleThetaCertificateActual | 463D6754... | 92352 B 5E6C94E8... | trio | actual conditional certificate |
| S2936ThetaUpperConstantActual | 7DF5C558... | 380288 B EC33F54B... | trio | actual ALGEBRA, not theta upper |
| S2944ThetaLinkRealization | A99FCAC3... | 18784 B E40D2C48... | trio | actual ALGEBRA, not theta upper |
| S2958HalfIQHullCertificateActual | DD0E8DB0... | 113144 B 16AA52D9... | trio | actual but tautological certificate |
| S2935HeightLeProcessionActual | 910E1A38... | 73272 B BDF40D69... | trio | actual conditional reductions only |
| S2941HeightUpperToProcessionAttempt | E1C4C2E5... | 44384 B E96E8848... | not probed; attempt | not actual bridge |
| S2945S2935Equivalence | 6679AC66... | 10144 B C863829A... | trio | bridge Props/trivial implications |
| S2932CorrectedCuspConsumerActual | 30A05C3E... | 145456 B 9112B2BB... | trio | actual corrected cusp consumer |

Full SHAs available in AUDIT_LEDGER entries 325-333 and in the artifacts themselves.

## 2. Corrected A6 chain: necessity of inputs

S2905Core takes:

```lean
hQ : S2882A6Q.IsStack etaleTopology
D : Pseudofunctor SignActionIndex (EtaleStackPseudofunctor F)
atBase : Equivalence (D.obj signActionObject) S2855HyperbolicOrbicurve.stack.fiber
generator_identification : ... ≅ S2857StackAuto alphaOverS2844
W : S2870QuotientWitnessData S2882A6Q hQ (S2869SignAction ...)
I : S2892Inputs hQ (S2869SignAction ...) W
```

- `hQ` is NOT proved, and is likely FALSE as stated. `S2893A6QIsStackActual`
  only proves `S2893A6QIsStack ↔ S2893A6QDescentAPI`; both sides are Props, and
  `S2893A6QEffectiveDescent` has no inhabitant. More fundamentally,
  `S1971ActionStackificationActual.lean` section 4 states that even a
  functorial pointwise colimit is ONLY A PRESTACK: 'its U-points see the trivial
  sign torsor, not arbitrary etale sign-torsors. The etale stack condition is a
  separate input.' So `S2882A6Q.IsStack` is an extra stackification hypothesis,
  not a consequence of the pointwise action-category construction. The correct
  object is a stackification/quotient stack (group B), not Q itself. This is a
  structural error in the corrected core's input, not merely an unproved field.
- `D` is not constructed. `S2882A6Q` is a strict pointwise Cat-valued functor
  (`S2882A6PFunctor.toPseudofunctor'`), not a stack quotient with the required
  equivalence `atBase`; the S2870 audit calls the quotient stack input missing.
- `W` is `S2870QuotientWitnessData`; no supplier.
- `I` contains `uniqueInput : S2883Inputs`, `groups : CoreGroupsInput`,
  `xK/cK/extensions`, `V/V_mod_bad`, `cusp : GenericCuspData cK`. These are
  genuine data, not the target, but none is fully constructed. In particular
  `S2883Inputs.classification : S2877OrderTwoAutClassification` and
  `underlying_ne_id_iff` are unproved; this is a legitimate reduction of the old
  false unique field, not target insertion.

`S2908CorrectedS`, `S2927Completion`, `S2928CorrectedT`, `S2934CorrectedT` are
assemblies/wrappers; none of the inputs is `SourceSignQuotientDataCorrected`, so
there is no direct circularity. However, the chain is **conditional on every hard
geometric object**. `S2934CorrectedT_arithmetic` is `rfl`; it does not prove a new
arithmetic identification.

`S2927Completion` additionally needs `I2892 : S2892Inputs` and `I : S2926Inputs`.
`S2926Inputs` contains corrected clauseA/B/C/D/F structures; each clause is a
bundle of concrete obligations (hstable, torsion23, imageContainsSL2, kernel-field
identification, multiplicative-37, q-comparison, kSide, localFamily, boundary).
Some individual inputs have actual suppliers (e.g. hstable S2798, cusp S2932),
but the full `S2926Inputs` is an input package, not a constructed theorem.

Verdict: actual conditional assembly; no literal circularity; massive input
front-loading/gap-shifting. Corrected T is not closed from source data.

## 3. IUT III source hull / theta upper / signed carrier

### 3.1 Raw source-hull no-go

`CertificateHullWiring.sourceThetaBound_unsat_of_degreeFaithful` is ACTUAL and
proves: if `hdeg : ∀ b, logDegreeAt 0 0 v (R.posRealAction (ofAdd b)) = b`, then
`¬ ∃ θ, sourceHullVolume v R n ≤ ofReal θ`. The proof uses
`sourceHullVolume_eq_top_of_degreeFaithful` (SourceImageHullVolume.lean:428):
the hull log-degree is unbounded, hence hull volume is `⊤`.

So the raw sourceHullVolume upper route is impossible **under `hdeg`**. This is
not absolute: `hdeg` is an explicit hypothesis, not proved for every
`SourceImageRealization`. If one insists on a non-degree-faithful realization,
hull volume may be finite, but no such actual realization is constructed in the
tree. Exact missing disjunction: prove every admissible source realization is
degree-faithful (then raw route is dead), or construct a non-degree-faithful one
with finite hull and the required comparisons.

### 3.2 Card-QCMP / Card-AMPL

- `QCMPComparisonSupply` (CardQCMPComparison.lean:85) is a structure with
  `selectedLowerPlaces`, q-parameters, `targetSigned`, and two comparison fields
  `q_le_theta`, `target_le_theta`. The comments explicitly say the fields are
  discharge obligations and that `targetSigned` is not claimed to have an
  object-level definition. No source instantiation is constructed.
- `CardAMPLThetaBoundSupply` (CardAMPLThetaBoundSupply.lean:78) similarly carries
  `realVolume_le_theta` as a field; `singletonRealSupply`/`nonempty_iff` reduce
  the supply to the same θ-bound content. It is a named interface, not a proof.

### 3.3 Card-HULLREAL signed carrier

`sourceSignedHullLogVolume = -sourceRealHullVolume`.
`sourceSignedHullCertificate` takes `hq : qSigned ≤ signedHullVolume` as an
explicit hypothesis, sets `thetaSigned := 0`, and uses the pre-supplied `hq`; it
does NOT produce the corpus (xi-f) comparison. `sourceSignedSurface_comparison_
not_forced_by_sign` correctly records that sign alone does not give
`qSigned ≤ hullSigned`. Under `hdeg`, `sourceSignedHullLogVolume = 0` (collapsed).

Missing exact signed-carrier fields:
1. an actual `qSigned` equal to the q-pilot signed log-volume (not arbitrary);
2. the (xi-f) comparison `qSigned ≤ -|log Θ|`;
3. a non-collapsed finite hull (`hfin`) or an ambient O-module carrier, since
   `hdeg` makes the value hull `top` and the signed carrier collapse to 0;
4. the relation of `thetaSigned` to `C_ThetaPaper` / the contract's θ-side.

`IQCarrier*` files (`IQCarrierConcreteModel`, `IQCarrierHaarData`) construct the
carrier only conditionally on a compactness/Haar input; `not_exists_iqHullLog
VolumeInterface_hull_subset/eq_of_degreeFaithful` show no carrier exists under
`hdeg`. This is the Card-HULLREAL gap.

## 4. S2935 / S2941 / S2945: ABC equivalence audit

- `S2935HeightLeProcession` is a **Prop**: for all ABC triples,
  `logHeight₁(abcJInvariant) ≤ (1/n) Σ collectionBound(D,Q,S,T)`. It is not
  proved. `S2935_height_le_procession_of_elementary` only reduces it to an
  elementary bound `6 log c + log 256 ≤ ...`, which is also unproved.
- `S2941HeightUpperToProcessionAttempt` is an attempt; no actual bridge.
- `S2945S2935Equivalence` defines `S2945AdditiveBound` **exactly as**
  `ABCHeightWeightAdditiveBoundV2` (the known ABC-equivalent additive bound) and
  `S2945Procession n`, then defines the two missing bridge Props
  `S2945AdditiveToProcessionBridge` and `S2945ProcessionToAdditiveBridge`. The
  theorems only apply the bridge hypothesis; no equivalence or bridge is proved.
  Thus the formal route is explicitly tied to the ABC-equivalent additive bound.

Verdict: S2935 is an ABC-strength height statement, not the paper's Cor 3.12.
S2945 confirms the gap is the height/procession bridge; it does not establish
equivalence with ABC, but it is clearly an ABC-type target, not a tautology.
There is no formal circularity; the issue is that this route **relocates** the
paper's tautological q-pilot computation into an unproved ABC-hard analytic
inequality. It cannot be justified as 'the paper step'.

## 5. S2936 (math audit only; no edits) and S2958

`S2936ThetaUpperConstantActual` is actual algebra: using S2966's
`rad ≤ absNormJ ≤ rad²` and S2937's actual `S ≤ Q`, it absorbs S/T into the
constant/region volume and derives an inequality of the form
`S2933ThetaUpper ≤ 6(1+eps) regionVolume + AJ`.

Correctness: as algebra, correct; no ABC assumption; no circularity; axioms trio.

Limitation: it does NOT prove `S2933Certificate.height_le_procession` or
`theta_le_region`; those are still explicit fields of `S2933Certificate`. It is
not a theta upper certificate. S2944 is the same algebra in thetaLink form.

**S2953 is definitionally circular too.** `S2953CThetaUpperCertificate` has fields
`hCTheta : CThetaPaper ... = thetaLogVolume / |Real.log q|` and
`hupper : thetaLogVolume <= CThetaPaper * |Real.log q|`. The second is forced by
the first (for `|log q| > 0`), and `hqAbs : |log q| = -certificate.qSigned`
defines the q-side. Thus `S2953_CThetaPaper_lower_bound` is a conditional
tautology over a certificate that already stores the desired upper inequality;
it does not prove the paper's C_Theta estimate. Do not cite S2953 as an actual
C_Theta upper/lower estimate.

`S2958HalfIQHullCertificate` is actual but tautological: qSigned = -1 and
thetaSigned = hullVolume + 1 (or 0), hullVolume from a half-IQ-hull W. The
certificate fields (`q_le_hull`, `hull_le_theta`, `q_negative`) are satisfied by
construction; no actual q-pilot/C_Theta content enters. It must not be cited as
the paper's nontrivial theta upper certificate.

## 6. Paper route verdict

### 6.1 IUT III Cor 3.12

Paper evidence:
- Statement III:10324-10360: defines `-|log Θ|`, `-|log q|`, concludes
  `C_Θ >= -1`.
- Proof III:10897-10898: 'follows formally'.
- III:929, 1038, 10902: 'two tautologically equivalent ways to compute the
  log-volume'.

Verdict: **independent of ABC, but tautological/structural**. It is not an
independent analytic upper estimate. The q-pilot log-volume is computed in two
ways by the multiradial algorithm; the inclusion `-|log q| ≤ -|log Θ|` is a
consequence of the construction, not an ABC-type bound. No ABC or q-pilot
ABC-type estimate is inserted. It relies on Theorem 3.11 (the deep multiradial
algorithm), which is the real unformalized input, not ABC.

### 6.2 IUT IV Theorem 1.10

Paper evidence: IV:1255 statement; IV:1376 applies `C_Θ >= -1`; IV:1583-1952
computes an explicit upper bound for `C_Θ` from div/sor/conductor data;
IV:1936 'upper bound for C_Θ'; IV:1952 final display.

Verdict: **independent**; no ABC hypothesis. The q-pilot normalization is
explicit (`|log q| = (1/(2l)) log q`, IV:1363 area) and comes from q-parameters,
not from ABC. ABC appears only as the final consequence. There is no visible
circularity in the paper text; the burden is on Theorem 3.11.

### 6.3 Our formalization vs paper

- S2951 `ThetaUpperTarget` is the correct **IUT IV** upper estimate shape
  `thetaSigned ≤ CThetaPaper * |log qParameter|`; its only actual estimate is
  the trivial C=0 (`S2951_thetaUpper_zero`). Missing nontrivial upper.
- S2935/S2941/S2945 are NOT Cor 3.12: they impose a J-height-to-procession
  inequality. This is an ABC-type height comparison, not the paper's tautological
  q-pilot computation.
- S2933 and S2936/S2944 treat `S2933ThetaUpper` (a candidate formula) and
  height/region certificates; they do not prove the paper's (xi-f) inclusion.
- S2958 is a tautological certificate, not the paper's C_Θ.

Overall: the paper route is not circular; Cor 3.12 is tautological, Thm 1.10 is
independent. Our formal route deviates: it tries to prove an ABC-strength height
inequality (S2935) instead of reproducing the tautological q-pilot computation.
This is a strengthening/gap relocation, not a circularity, but it cannot be sold
as the paper's step.

## 7. Unqualified / do-not-cite list

- S2905/S2908/S2927/S2928/S2934: actual **conditional assemblies**; not
  unconditional corrected T.
- S2933Certificate: `height_le_procession` and `theta_le_region` are inputs.
- S2935HeightLeProcession: Prop, not proved; only conditional reductions.
- S2941: attempt, not actual bridge.
- S2945: bridge definitions + trivial implications; no equivalence.
- S2936/S2944: algebraic constant absorption; not theta upper.
- S2958: tautological certificate (q=-1, theta=hull+1); not C_Θ.
- S2952: trivial certificate.
- S2951: source-only, trivial C=0 estimate; no olean.
- S2919/S2922/S2923 fixed-constant versions: invalid for final.
- S2923HeightBridge: only `S2923_heightBridge_of_input` conditional.
- Raw source-hull upper: no-go under hdeg; no non-degree-faithful actual.
- Card-HULLREAL signed certificate: comparison is a hypothesis, qSigned arbitrary.
- Card-QCMP/AMPL: structures whose fields are obligations; no source instantiation.

## 8. Precise missing objects (highest value first)

1. `S2893A6QEffectiveDescent` / `S2882A6Q.IsStack` inhabitant (or a proof of
   effective descent for the pointwise quotient Q). This unlocks hQ and thus
   D/atBase/W. Why not gap-shifting: it is a concrete descent theorem for a
   constructed Cat-valued functor, and S2812's IsStack machinery is actual for
   representable stacks; the work is to adapt it to the quotient.
2. Constructed quotient stack `D` with `atBase` equivalence and
   `generator_identification`, plus `S2870QuotientWitnessData W`. This is the
   actual corrected stack quotient; without it the corrected A6 core is only
   conditional. Why not gap-shifting: concrete stackification/quotient object,
   not a restatement of corrected S.
3. `S2877OrderTwoAutClassification` + `underlying_ne_id_iff` (S2883Inputs).
   This is a concrete classification of order-two endomorphisms of S2844X;
   it unlocks the corrected unique-involution field without assuming the target.
4. Non-degree-faithful finite source-hull realization OR proof that every
   admissible realization is degree-faithful. Then construct the actual signed
   q-pilot `qSigned` and prove the xi-f comparison `qSigned ≤ -|log Θ|`. This is
   the actual Card-HULLREAL gap, not an arbitrary certificate.
5. Actual q-pilot/C_Theta upper estimate for S2951 (`thetaSigned ≤ CThetaPaper *
   |log q|`), with an actual q-parameter identification. This is the genuine IUT
   IV upper estimate; it is not obtained by S2936/S2944/S2958.
6. Full `S2926Inputs` clauseA-F actual suppliers (hstable, torsion23,
   imageContainsSL2, kernel field, multiplicative-37, q-comparison, kSide,
   localFamily, boundary), respecting corrected restatement and no forgetful
   old-S route.

## 9. Top three construction tasks (not gap-shifting)

### Task A — Prove effective descent for S2882A6Q
Target: `S2893A6QEffectiveDescent` (equivalently `S2882A6Q.IsStack`).
Method: adapt the S2812 IsStack/descent proof (which is actual for the
representable etale pseudofunctor) to the pointwise quotient functor
`S2882A6Q`: descent data are pointwise quotient maps; gluing uses the yoneda
sheaf and the quotient's universal property. This is a concrete theorem, not a
restatement of corrected S.

### Task B — Construct the corrected quotient stack D and W
Target: `D : Pseudofunctor SignActionIndex (EtaleStackPseudofunctor F)` with
`atBase` equivalence and `generator_identification`, plus
`S2870QuotientWitnessData`. Method: use the effective descent from Task A to
stackify the pointwise quotient; construct the action groupoid/quotient stack
and the generator comparison from the actual `S2857StackAuto`. This directly
fills the largest missing object in S2905.

### Task C — Card-HULLREAL signed q-pilot comparison
Target: actual `qSigned` (q-pilot log-volume) and proof
`qSigned ≤ -|log Θ|`, with a finite non-collapsed hull. Method: either prove
degree-faithfulness is unavoidable and switch to the ambient O-module carrier
(`not_exists_iqHull...` explains why value hull collapses), or construct the
non-degree-faithful finite realization and prove product-edge normalization
(`sourceHullVolume_le_imageVolume_of_productEdgeNormalization`) plus the
xi-f comparison. This is the concrete analytic identity missing from Card-HULLREAL,
not a restatement of C_Theta.

All three are construction tasks with concrete targets; none assumes the
conclusion. The paper's tautological Cor 3.12 route is not one of them;
reproducing the paper would instead formalize Theorem 3.11's multiradial
algorithm and the q-pilot computation, which is a different (larger) task.
