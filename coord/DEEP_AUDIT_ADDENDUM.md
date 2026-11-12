# Deep audit addendum — residual (xi-f) card, signed carrier, board

Date: 2026-11-07. Complements coord/DEEP_AUDIT_ABC_IUT.md.

## 1. Exact residual card text

`SourceProcessionStepXIInclusionResidual.lean` states and proves:

- Route 1 (V2-constructor side): CLOSED, DEGENERATE. All in-tree real hull
  carriers are nonnegative (`iqHullRealVolume_nonneg`, `sourceRealHullVolume_nonneg`),
  all in-tree q candidates negative; the literal inclusion follows from
  `negativeValue_le_of_nonnegative` and consumes no hull value. The file says
  'zero discriminating power'.
- Route 2 (hull-side reverse estimates): BLOCKED. A non-degenerate reading needs
  a signed carrier `hullValue = -|log Theta| < 0`; none exists. IQ interface
  logVolume is ENNReal-valued; under degree faithfulness no finite real upper
  value exists (`sourceThetaBound_unsat_of_degreeFaithful`).
- Route 3: signed-surface counterexample shows sign constraints alone do not
  force `q <= hullValue`.

So `sourceProcessionStepXIXifInclusionResidual` is an interface obligation, not
a signed carrier. Any citation of the literal (xi-f) inclusion as `C_Theta >= -1`
is invalid: the file itself labels it reduced/pinned form with zero discriminating
power.

## 2. Card-AMPL / Card-QCMP exact gaps

- `CardAMPLThetaBoundSupply.nonempty_iff` says a supply exists exactly when some
  `theta >= 0` bounds `W.logVolume W.hull`; `singletonRealSupply` is a one-point
  consistency witness, explicitly 'not a model of the paper's carrier'.
- `QCMPComparisonSupply` has `targetSigned : Real` as a field and comparison
  fields `q_le_theta`, `target_le_theta`; comments say no source instantiation
  and no object-level definition of `targetSigned`. This is a named supply, not
  a construction.

## 3. Signed carrier missing fields (restated)

1. actual `qSigned` = q-pilot signed log-volume (not arbitrary real);
2. `qSigned <= -|log Theta|` (xi-f comparison);
3. non-collapsed finite hull (`hfin`) or ambient O-module carrier; degree-faithful
   value hull is `top`;
4. `thetaSigned` related to `CThetaPaper` / actual theta upper.

## 4. Board status

`coord/DEEP_AUDIT_TASK_BOARD.md` records A-E, task IDs, owners, scopes, and
dependencies. Board limit 256 was reached, so E is merged into task-702 pending
Lead slot management. A/C are ready and scoped; B/D lack scope arrays because
they are blocked and only Lead can edit them.

## 5. Subagent C result (Card-HULLREAL signed q-pilot)

New file: `tmp/sheaf/xif/paper/S2981SignedQPilotActual.lean`,
935 lines, source SHA256 `7A1F25419C3DEEF289B983EB0DEA8D555B65FB65A9507DC120B46980FE19ECC4`;
olean 420680 B SHA256 `416C1AF58D1359D7EE308EAC06193CA130F8E5C6435F27197F0483A96CA41E7D`;
fresh compile EXIT=0; axioms trio for key declarations; no sorry/axiom.

Proved (kernel-checked):
- `sourceQPilotSignedLog` is the actual theta-packet q-pilot `-|log q|`, and equals
  `-|logDegreeAt ... (posRealAction q)|`.
- `sourceRealHullVolume_eq_zero` **unconditionally**: the value-realized source
  hull is a submonoid; a positive-degree point gives unbounded powers and hull
  volume `⊤`; otherwise all log-degrees are nonpositive and hull volume `0`. In
  both phases `.toReal = 0`. No hdeg premise.
- `sourceSignedHullLogVolume_eq_zero`; `sourceXifSignedComparisonAtQPilot_unconditional`
  is therefore `qPilot ≤ 0` (true, but zero discriminating power).
- `not_nonempty_sourceSignedQPilotCarrier`: the non-collapsed signed carrier is
  empty for every realization.
- `sourceQPilotHullBound_iff_hullVolume_eq_zero`: the q-scale bound is equivalent
  to the collapsed zero phase, not a positive finite bound.

Exact missing object (group C): an **ambient IQ/O-module carrier**
`IQ(S±_{j+1}; n,∘D^vdash_{vQ})` with ring-of-integers/O-module structure and Haar
log-volume, whose hull is a bounded `λ·O` region, not the least scaling-stable
value submonoid. The ambient numeric residual is `ld(λ)+C ≤ |log q|`
(`sourceQPilotHullBound_of_scaledRegion`); it cannot cure the value-layer
collapse. Do not add `0 < sourceRealHullVolume` as a hypothesis: it is refuted.

## 6. Subagent D result (S2883Inputs / classification)

New file: `tmp/sheaf/xif/paper/S2982A6SourceDataActual.lean`,
source 11777 B SHA256 `1D671B4388716B056CC01074D1547885C55003E98C5B3F43E79428F9648ECC62`;
fresh compile EXIT=0; olean 170640 B SHA256 `519B7411F9D2F99B7DE60642EC7BB370922FFC01E885BF224CE08F978399B0B8`;
axioms trio. (An earlier 41520 B olean was stale; current fresh compile is canonical.)

Proved:
- `S2982_underlying_id`, `S2982_underlying_ne_id_of_ne`.
- `S2982_underlying_ne_id_iff_iff_reflects`: the S2883 equivalence is equivalent
  to `S2982UnderlyingReflectsId`.
- `S2982_rigidity` + `S2982_app_eq_of_underlying_eq` => `S2982_reflectsId`,
  so `S2883Inputs.underlying_ne_id_iff` is **unconditional**.
- `S2982Inputs_of : S2877OrderTwoAutClassification -> S2883Inputs`; the
  classification is now the only field.

Audit finding (mathematical, not Lean-proved): `S2877OrderTwoAutClassification`
is likely **FALSE**: `S2844X` is projective E37 `y²+y=x³−x` over ℚ(i) with full
rational 2-torsion, so translation by a nonzero 2-torsion point is an order-two
automorphism distinct from identity and from `alphaOverS2844`. No translation
automorphism is constructed in the tree, so this is an audit claim, not a Lean
counterexample. The old full-scheme classification must be replaced by an
origin/cusp-preserving version; `S2902UniqueData.origin` and S2902/S2990 wrappers
are unsatisfiable as stated. `S2892Inputs` itself remains input data.

Next executable: prove `S2844InfinityOver ≫ S2877Underlying inv = S2844InfinityOver`
(underlying map preserves marked cusp), then reformulate classification as
origin-preserving; with `S2982_reflectsId` this is genuine.

## 7. Subagent B result: D/atBase/generator actual; hQ REFUTED; W vacuous

New file: `tmp/sheaf/xif/paper/S2980QuotientStackActual.lean`,
288 lines, source SHA256 `916299C689DA292D7071B255F9A4B55ABF1E357388157E9D0C7B7171CAC6621D`;
olean 175528 B SHA256 `A14E19B6B9EB17B83F9255FBF2A4839DE9DD3C5924EE54DA906D2B578682A7D9`;
fresh EXIT=0; key axioms trio.

ACTUAL:
- `S2980D : Pseudofunctor Iut.SignActionIndex (EtaleStackPseudofunctor F)`;
  every object is the representable stack of `S2844X`; generator maps to the
  actual elliptic involution `S2857StackAuto alphaOverS2844`.
- `S2980AtBase`: identity adjoint equivalence to `S2855HyperbolicOrbicurve.stack.fiber`.
- `S2980GeneratorIdentification`: unitor iso.
- `S2980A`: actual `OrbicurveSignAction` from `S2869SignAction`.
IMPORTANT CORRECTION: D is the sign-action DIAGRAM on the source curve X_F, not
the quotient stack `[X_F/sign]`; `atBase` forces `D.obj star ≌ X_F`. The quotient
`cF = S2891CF hQ` is separate.

REFUTED / VACUOUS:
- `S2975b_not_isStack : ¬ S2882A6Q.IsStack` and `S2993_not_isStack`; also
  `S2993_not_isPrestack` (`¬ IsPrestack`). Empty-base hom-presheaf obstruction.
- `S2980W_vacuous : (A hQ W) -> False`, so `S2870QuotientWitnessData S2882A6Q hQ A`
  is vacuous. `hQ` is refuted, not merely unproved.
- Exact first Lean error for W: failed to synthesize `Pseudofunctor.IsStack
  S2882A6Q (etaleTopology F)`; even granted hQ, first field is the quotient
  invariant morphism, then the universal property.

Forced route 3: replace `S2882A6Q` by a stackification `Q'` (torsor stack
`[X_F/SignGroup]`), prove `IsStack Q'`, prove a fiber equivalence `Q' ≃
`S2882A6Q`, and restate `S2870QuotientWitnessData`/`S2905Core` with `Q',hQ'`.
`S2994/S2996/S2995` only give specs/targets; no `Q'` is constructed.

## 8. Subagent A result: effective descent no-go reduction; target not inhabited

New file: `tmp/sheaf/xif/paper/S2979EffectiveDescentActual.lean`,
16102 B source SHA256 `279DC71F5BE0D857EB3D29F69599CD59FBD66CAC240D5FF76705875FA5344DC2`;
fresh `-o` olean 235720 B SHA256 `CDA2416F8C9E3E37007DB90EA0DCE006D0A0D3DDDEB1654B01EDED5FD4C49185`;
EXIT=0; all key theorems axioms trio; no sorry/axiom/placeholder.

Proved:
- `hom_twist_eq`: the twisted-object equality for a descent datum.
- `descentFamily_compatible_of_twist_one`: the S2812 compatible-family gluing works
  exactly when all descent twists are `1`; the twist is the only obstruction.
- `twist_conj_of_iso`: single-index self-twist conjugation; the naive two-index
  form is false and is not claimed.
- `not_effective_of_nontrivial_selfTwist`, `not_target_of_twist`,
  `not_isStack_of_twist`: conditional no-go `S2979CanonicalTwistTrivial ->
  S2979NontrivialSelfTwist -> ¬ S2893A6QEffectiveDescent / ¬ IsStack`.

Missing inputs:
- `S2979CanonicalTwistTrivial` (expected true; technical instances-transparency
  blocker when unfolding `toDescentData`/`mapComp'`);
- `S2979NontrivialSelfTwist` (geometric: nontrivial etale SignGroup-torsor with
  equivariant point; no such cover/descent datum in tree).

Conclusion: group A is a no-go/stackification reduction, not a positive
inhabitant. Group B's stackification/quotient stack is the correct positive object.

## 9. S3048 / A2 effective descent / R0 / connected site

- `S3048MeasureLowerBoundActual` ACTUAL: source 4045 B SHA
  `DCBBDFDF44629ED51419563C021AFC616C308905752D48C54B26E0EF106757CB`; olean 371920 B
  SHA `3DD923EAC6871DDBC40355191A33C403A51D658E75962152D93DE87EE8C711EF`;
  `S3048_measureLowerBound`/`S3048_CTheta_nonneg` axioms trio. hscalar actual-parameter
  case closed via S3049 bridge.
- A2 effective descent UNCONDITIONAL: `S3042b_QEffectiveDescent` (S3042b, source
  SHA `4B5D2B94...`, olean 92408 B SHA `9E484359...`). This proves `S2893A6QEffectiveDescent`
  (EssSurj), NOT `IsStack`: B's S2975b/S2993 still prove Q is not a prestack.
- **R0 bridge is ACTUAL** (correction): `S3042R0Bridge` source 4864 B SHA
  `ED628B004627B755F1EC2ED44D44FC886AE4D9DF697729D9A69F994AE273E8C4`; olean
  224224 B SHA `F3C8EE2B0EC2F3E0E3336F2B2D6C3F16A2ADEBC4E39B20BB96A8A740059A0EDE`;
  axioms trio. `S3053UnconditionalAffineClassification` ACTUAL (source 1989 B SHA
  `F55E6B7DD9459EBB346855AD6293B59D9FE236FD741F06F68853A3CB9520541F`; olean
  13736 B SHA `B75EAACBE10441057E176A8F4816964A33C153D9B081CB51C270A4EDB93A23BD`).
  Affine classification is CLOSED; the only S3030 gap is projective transport
  (`S3053ProjectiveTransportTarget := S3041SchemeClassFromAffine`).
- Connected site: `S3050ConnectedSite` only defines the site/property/Q targets;
  prestack is NOT proved. `S3050QIsPrestack`/`S3050QIsStack` are Props. Q'
  stackification remains missing.

## 10. S2913OriginToChart refuted (S3060)

`S3060ChartZFromOriginToChart` ACTUAL (source 3975 B SHA
`4FBE51A0A7722B6D4251944AAE805666999DD395DF52A52236886E566E0219D3`; olean 37088 B SHA
`CADA7FF830EC8EC0ECAEEFBA6DFD458284D296594E2FB02C3E05765A999C9842`):

- `S3060_originToChart_false : ¬ S2913OriginToChart`.
- Proof: apply `S2913OriginToChart` to `β = 1` (order-two, origin-preserving).
  `S2913ChartFactorization.hoverlap` forces the chart-Z factor to be `alpha`;
  chart-Z/chart-Y comparison plus `S3057_gluingUniqueness` yields
  `1 = alphaOverS2844`, contradicting `S2876_alphaOverS2844_ne_id`.

Consequences:
- `S2990Inputs.originToChart` cannot use `S2913OriginToChart`.
- S2990/S2902 wrappers depending on it are vacuous or must use a **branch-dependent**
  factorization: `z = id` on the identity branch, `z = alpha` on the alpha branch.
- `S3030`/`S3053` affine classification does NOT depend on S2913; still valid.
- Projective transport still needs chart-Z preservation + chartY compatibility,
  now via branch-dependent factorization.

## 11. S3063/S3064 chart-Y nonoverlap algebraic core CLOSED

- `S3063ChartYNonoverlapActual` ACTUAL: source 4767 B SHA
  `0584F2A523294F335D4C13195C12A83B488575D5D332F8CA0FF8386857620619`; olean 120648 B
  SHA `D18186A13860900798AA04D145606B9573C84A27CB00AC0366A032D47107478C`.
- `S3064InfinityIdealSpanActual` ACTUAL: source 5150 B SHA
  `7360F66BF91BFE3F43BE9D4F34D0C9AA5BB5848735AE16C4AEF06FF65CB8D005`; olean 130208 B
  SHA `AA9A5392F62ACCBBFE9ABFFF6C012CBBB9B94AB485A481BA80F21B9DAAF00604`;
  `S3064_span_eq_infinityIdeal`/`S3064_infinityIdealSpan` axioms trio.
- S3063+S3064 close the chart-Y nonoverlap algebraic core. Projective transport
  still needs chart-Z preservation + chartY compatibility; connected-site prestack
  and Q' stackification remain separate gaps.

## 12. S3068 hxi refined conditional chain

`S3068GlobalReadoutLeActual` ACTUAL (source 3027 B SHA
`A04B12576164BDBEE61750FB5EEDA530B5CF7426F56658D5E5D0BE881053B85C`; olean 23416 B SHA
`E7FB0E5A7E3C1FEFCF58F20BB0242B91F1C0258ACD7021EDF161F3329E6275C3`):

- `S3068GlobalReadoutLe_of_native` takes
  `S1675OneColumnNormalization` + `S1675HullNativeMagnitudeBound` and yields
  `S3068GlobalReadoutLe` (`globalThetaHullLogVolume <= qPilotMagnitude`).
- `S3068GlobalReadoutLe_iff_condition` identifies it with `GlobalComparisonCondition`.
- Exact first unproved subformula: `S1675HullNativeMagnitudeBound`.
  `S1675OneColumnNormalization` is the other explicit input.
- Local formula identity remains `GlobalQVFamThetaHullSumActual.LocalThetaHullFormulaGap`.

## 13. S3065/S3066/S3071/S3072 status

- `S3065ChartYNonoverlapActual` ACTUAL (source SHA `2832E5B4...`; olean 60400 B SHA
  `66FB3551...`; `S3065_chartYNonoverlap`, `S3065_pointRealization`).
- `S3066ChartYOverlapPreimageActual`: `S3066_chartYOverlapPreimage` ACTUAL (source SHA
  `39647CD4...`; olean 50568 B SHA `537712A5...`). A separate S3066 instance attempt
  has a first error (scheme GlueData instance/probe), not a failure of the proved theorem.
- `S3071TorsorGroupoid` and `S3072QPrimePseudofunctor` are TARGET-DEFINITION actual
  (olean 56960 B/112040 B), not constructed witnesses: S3072 target/Prop specs only.
- hxi two producers (`S1675HullNativeMagnitudeBound`, `S1675OneColumnNormalization`)
  are in progress; S3068 remains their conditional consumer.

## 14. S3079 actual; S3068 open-immersion instance vs lift/factorization first error

- `S3079PaperAlignmentQCoeffActual` ACTUAL (source SHA `B2F6AF73...`; olean 100616 B SHA
  `A67247AB...`; S3079 unit/stepV coefficient identities axioms trio).
- `S3068_chartZ_isOpenImmersion` is elaborated actual (axioms trio), but the containing
  file `S3068OpenImmersionFactorizationActual` is EXIT=1:
  `S3068_lift` and `S3068_factorization_of_range` fail at lines 43/63 with
  `?m.19 ≫ Over.Hom.left β : ?m.13 ⟶ Over.left S2844X` expected
  `↥(E37ProjGluedScheme K e)`. This is a type-path issue between `Over.left S2844X`
  and the glued scheme; no olean. Do not cite lift/factorization as actual.
- `S3068PointRealizationClosed` ACTUAL (olean 4672 B SHA `C6725146...`).
- hxi producers still in progress.

## 15. S3066/S3067 point realization; S3073/S3076b/S3078b/S3079/S3080 actual

- `S3066_chartYOverlapPreimage` ACTUAL; `S3067PointRealizationActual` ACTUAL
  (source SHA `CB256D84...`; olean 24352 B SHA `B27B876E...`; `S3067_pointRealization`).
- `S3068OpenImmersionFactorizationActual` still EXIT=1 (lift/factorization type path);
  S3068 syntax/type repair in progress.
- `S3073TorsorPullbackActual` ACTUAL definitions (source SHA `11ADA33F...`; olean 70904 B
  SHA `C81642F2...`).
- `S3076bSourceNativeQBridgeAttempt` ACTUAL (source SHA `37D847FC...`; olean 68952 B SHA
  `AD403FA9...`; `S3076_weightedBridge_of_exactMissingEq`).
- `S3078bTopologicalCoverGraphConnected` ACTUAL (source SHA `5DE4FBD3...`; olean 15320 B
  SHA `D57F0C13...`).
- `S3079PaperAlignmentQCoeffActual` ACTUAL (previous section).
- `S3080PaperConstantActual` ACTUAL (source SHA `DAEFA2DF...`; olean 116480 B SHA
  `C2A3B866...`; `S3080_coeff_eq_iff`); `S3080S3081AttemptActual` olean 28376 B.
- hxi two bridges still missing.

## 16. S3076/S3101/S3073/S3077/S3100 actual; remaining gaps

- `S3076QPrimeNatIsoActual` ACTUAL objectwise mapId (source SHA `8D502D5E...`; olean
  32048 B SHA `AF4789F6...`).
- `S3101IndexAuditActual` ACTUAL (source SHA `736B098C...`; olean 34520 B SHA
  `DC701350...`): C3 tensor block/region identities actual; missing
  `S3101IndexCardEquality` and `S3101BaseFieldEquality`.
- `S3073TorsorPullbackActual` restriction ACTUAL.
- `S3077QPrimeCoherence` ACTUAL mapId component (source SHA `BB5303FD...`; olean
  124712 B SHA `053F9A6B...`); **mapId naturality and mapComp unproved**.
- `S3100ActualGlobalHullBoundAttempt` target ACTUAL definitions (source SHA `58E473FA...`;
  olean 65600 B SHA `3F458287...`); `S3100FieldAuditActual` ACTUAL. **S3100 C3/native
  numeric comparison UNPROVED** (`S3100FirstUnprovedInequality` + index/base-field
  equalities).
- **S3100 sourceHull degenerate/unusable**; must use globalThetaHull / C3 Haar carrier.
- S3095/S3096 remain conditional ACTUAL.
