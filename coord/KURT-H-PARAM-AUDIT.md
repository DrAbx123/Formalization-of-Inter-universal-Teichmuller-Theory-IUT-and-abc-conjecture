# Kurt lane explicit-parameter inventory (2026-11-17 18:05Z)

Rule (Lead): explicit parameter/conditional interfaces are UNPROVEN OBLIGATIONS; they do not count
as closed nodes or accepted results. This page lists the ones in the kurt lane, their equivalent
unproven object, the owner, and the real construction plan.

## U-R (C2/C3, hP5, J1-M)

| parameter | appears in | equivalent unproven object | owner | construction plan |
|---|---|---|---|---|
| hvol (bridge hypothesis) | Mzk1URThetaKHP5BridgeActual.neg_MpaperV2_le_thetaLam_of_bridge ; Mzk1URThetaKJ1BridgeActual.j1_same_q_bridge | S <= M_paper_v2, S = sum_b thetaLamWeight_b*urCeilC_b*log p_b | kurt+david | replaced by the correct-direction hbridge_of_fiberLe (DONE 00:34:55) or by J1-M mass route (Q1-Q3 approved) |
| hbridge_of_fiberLe (per-b fibre comparison) | Mzk1URThetaKHP5J1SameQActual | per-b [F:Q]*2l*thetaLamWeight_b*(urCeilC_b*logp) <= fiberQTerm_b | kurt+david | base-change tower ord_P = e_P*ord_b + fiber_sum_ef telescope (david OrdTower), or J1-M mass route |
| hperB (per-b packet bound) | Mzk1URThetaKC3UpperActual.theta_lam_le_Hpkt_of_hperB | ksThetaHullLog b <= urPacketV_K b | kurt | Mzk1URPacketActualInstanceActual.ksThetaHullLog_le_urPacketV_K (in compile; needs J1Support/KLowerBound oleans) |
| hstepVIII (lambda weighted) | Mzk1URThetaKC3UpperActual.C3_upper_route ; theta_lam_le_paperRHS | Sum_b thetaLamWeight_b*urPacketV_K_b <= kappa*(...) - M | david/kurt | Mzk1ULStepVIIILambdaActual.hstepVIII_of_collectionLayer_gen + hM_lambda; hii/hsQ via hii_arith/hsQ_arith |
| hM (M paper = sum w Q/(2l)) | gen hstepVIII / C3 | M_paper_v2 = Sum_b thetaLamWeight_b*Qb_b/(2l) | david | MpaperB_eq_ordB + M_paper_v2_eq_sum_Qb_div |
| hprime | C3_upper_route | paperLstarLogs <= (4/3)*paperEar | andrew | Mzk1UHprimeActual.hprime_paperLstarLogs_le (thin instance of Mzk1ULHpktActual.hprime_paperConstants) |
| hconst | C3_upper_route | 2 log l + 56 <= (4/9) E_ar | accepted | ul_hconst_of_paperConstants |
| ThetaMScaleData.eFiber | Mzk1URThetaKLambdaMScaledActual | e_{P|b} (F-fibre ramification) | david | Mzk1ULThetaMWeightActual.eFiber (DONE 00:48:22) |
| thetaP5M (M-scale theta) | new theta-source hull route | corrected theta reading with coefficient v_p(q_b)/(2l) | kurt | Mzk1URThetaSourceHullOActual (O-saturation; in compile) + Kummer mass + same-coefficient equality |
| HaarScaleData (Layer 2) | Mzk1URThetaKKummerMassActual | Haar scaling factor value (c = ||a||^finrank) | kurt | DVR index (cardQuot_pow_of_prime/absNorm_*) + Haar subgroup index (Subgroup.index_mul_measure); Layer2 to be DELETED once proved (not terminal) |
| hperB in C3 legacy | C3_upper_route_legacy | same as hperB | kurt | INTERIM/LEGACY only, not terminal |

## B1-B (analytic h)

| parameter | appears in | equivalent unproven object | owner | construction plan |
|---|---|---|---|---|
| hBranch (all rational) | Mzk1G1PsiCauchyM2TargetActual.m2AnalyticTarget_of_rationalBranch | Branch subset of Q-points | kurt | general lex induction over M2Producer.AlgPoint (muMeasure_wf) replaces this |
| Cauchy chain inputs (hB coefficient bounds, hroots unit disc) | CoeffEval/DerivativeEval/Consumer | coefficient/root bounds for the actual branch polynomials | kurt | from minpoly + unit-disc conjugate hypothesis (batch 3b) |
| M2AnalyticTarget witness components (m2AnalyticTarget_of_witness) | henry Mzk1G1PsiM2AnalyticAssemblyActual | q, deg>0, branch values in {0,1}, critical values in {0,1}, 0 avoided | henry+kurt | assemble via M1 base + lex induction; critical values from pre-ported TauCeti |

## Note
- All rows above are OBLIGATIONS, not results. Only rows whose "construction plan" is DONE with three
  axioms should be reclassified; see the watchdog DONE lines.

## Addendum (2026-11-17 20:25Z, andrew hC4 cross-check): per-lambda C4 obligation

andrew's cross-check of uc_c4_actual_paper_letters vs D1Letters.hlarge shows the C4 letters are at
the GLOBAL IUT data layer (Q/M passed as reals, S_ar/eMod global), while hlarge needs a PER-lambda
instance: (1/6 - 2/l^2)*jHeight lam <= (1 + 12 dmod/l) S + 10(emod*l + eta), S <= discOver K +
truncConductor lam. Therefore:
- a per-lambda C4 instance is required (Q := jHeight lam with its own hP5/htheta/hstepVIII);
  the current global C3_upper_route/theta_lam_le_paperRHS only give the global scalar once;
- S_ar (global) vs S (per-lambda) requires the tripodal per-lambda upper bound
  SAr_tripodal T <= discOver K + truncConductor lam (david hcond/logDiff lambda);
- emod must be eStarMod (eMod T) and eta := etaPrm;
- C4 fixes l = prime >= 5 while D2/D4 choose l per lambda (sqrt h <= l <= C_d sqrt h log) -
  requires kurt/david confirmation or a substitution.
Status: D1AnalyticInput CANNOT be de-parameterized yet; recorded in
coord/P8-DEPENDENCY-AUDIT.md section 6. This is an OBLIGATION, not a closed node.

## Addendum 2 (2026-11-17 21:00Z): per-lambda C4 refined (david/andrew/Lead ruling)

- l: per-lambda l_lam is chosen from the EXCLUSION SET satisfying both l>=5 and the D2 second bound
  sqrt h <= l <= C_d sqrt h log(2 C_d h) (route L574, L581-587); no "fixed l conflict": C4 holds
  for each admissible Theta-data; D4 absorption puts the log(2 C_d h) dependence into C_d
  (route L634-636). [Lead ruling]
- per-lambda C4 inputs: Q := jHeight lam, M := jHeight lam/(2l), S := discOver K + truncConductor lam
  (NOT global SAr_tripodal; hence hlarge.hSD is le_rfl, no new per-lambda S upper bound),
  dmod := dMod T, emod := eStarMod (eMod T), eta := etaPrm; hP5/htheta/hstepVIII instantiated per lam.
- Remaining true obligations for per-lambda S: log d_Ftpd = discOver K (logDiff_eq) and
  log f_Ftpd <= truncConductor lam (hcond), both from Legendre equality + per-place conductor.
- Reuse candidates (repo recon, david+andrew): Mzk1G1D1LettersActual (hSD field, d4_of_c4_qscale),
  Mzk1G1LocalHeightCriterionActual (discOver/truncConductor/IsBadPlace),
  Mzk1ULHSQFinalActual (log_sQOf_le_of_perPlace/hsQ_paper_shape),
  Mzk1ULTripodalConductorActual (sQOf/log_sQOf_eq),
  Mzk1HTF3ConductorHeightActual (TruncatedConductorHeightData, DONE),
  Mzk1G1JHeightUniformActual.height_dictionary_deg (jHeight = Q_all),
  Mzk1P6HConstActual.eStarMod (emod).
- Kurt side: C3_upper_route / theta_lam_le_paperRHS are global scalar forms, reusable per lam by
  passing Q := jHeight lam, M := jHeight lam/(2l), and the lambda-weighted hstepVIII
  (Mzk1ULStepVIIILambdaActual.hstepVIII_of_collectionLayer_gen + hM_lambda).
- Principal-lattice mass (Lead-approved): J1-M mass now uses
  arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic_of_generator
  (Mzk1URThetaKMassActual.principal_lattice_mass); HaarScaleData is NOT in the main chain
  (fallback only).

## Landed DONE donors (verified watchdog DONE, three axioms) - reuse record

- Mzk1ULStepVIIILambdaActual (DONE 12:29:43): weighted_logP_aggregate_le, weighted_sum_nonneg,
  hstepVIII_of_collectionLayer_gen (outer weight w fully parameterized; w := thetaLamWeight gives
  the paper-faithful StepVIII intermediate, w := nativeBadLocalWeight recovers legacy).
- Mzk1ULFiberSumActual (DONE 11:23:10): fiber_sum_ef (Sum e_P f_P = [F:Fmod]),
  qPilotMagnitudePaper_v2_expand.
- Mzk1ULOrdTowerActual (DONE 10:51:48): count_nsmul, localOrderAt_mul, localOrderAt_pow,
  localOrderAt_map_pow, ord_algebraMap_eq_e_mul_ord (ord_P(algebraMap q) = e_P * ord_b(q)).
- Mzk1ULLocalOrderActual (DONE 00:55:33): localOrderAt, localOrderAt_def, localOrderAt_nonneg,
  localOrderAt_span.
- Mzk1ULThetaMWeightActual (DONE 00:48:22): eFiber, eFiber_pos, thetaMWeight,
  thetaMWeight_mul_thetaLamWeight (= 1/(eFiber*dModF)), urPacketV_K_M.
- Mzk1ULQSelectedActual (DONE 10:53:17): selectedFPlace, selectedIdeal, fiberTerm, QSelected,
  hMinusQ, qPilotMagnitudePaper_v2_eq_QSelected_add_hMinusQ.
- Mzk1ULSerreWildBoundActual (DONE 00:57:23): count_lt_of_not_pow_dvd,
  differentExponent_lt_of_not_pow_dvd.
- Mzk1ULKPlaceAlignmentActual (DONE 00:20:11): cSelected, orderAtFPlace_eq_cSelected, cSelected_def.
- Mzk1ULLegendreTwoTorsionActual (DONE 10:39:02): legendre_j_eq_jOfLam, legendre_negY_zero,
  legendre_mem_twoTorsion_of_x, legendre_not_mem_twoTorsion_of_y_ne.
- Mzk1ULHlogKHSULambdaStatementsActual (DONE 10:03:26): HlogKLambdaData, HsQrawLambdaData,
  WildBoundData, hlogK_lambda_shape, hsQraw_lambda_shape (lambda-shaped letter interfaces; the
  numeric bounds remain david's obligation).
- Mzk1ULS (P6C3C4Actual) (DONE 10:55:42): kappa, cL, c3_to_c4, c4_display.
- Mzk1URThetaKHP5J1SameQActual (DONE 00:34:55): MpaperV2_eq_fiber_sum, j1_ksRootCoeff_le_urCeilC,
  qVFamNormalizedCoefficient_le_twoL_mul_urCeilC, hbridge_of_fiberLe,
  neg_MpaperV2_le_thetaLam_of_fiberLe.
- Mzk1URThetaKJ1SupportActual (DONE 10:17:54): mem_ksThetaPossibleImages_iff, ksThetaPhi_id_mem,
  pureGenerator_smul_subset_possibleImages, possibleImages_subset_packetHull.

## Heartbeat registry (kurt lane, Lead-approved)

1M: Mzk1URThetaKLowerActual, Mzk1URThetaKSideActual, Mzk1URThetaKHP5LamActual,
Mzk1URThetaKHP5BridgeActual, Mzk1URThetaKLambdaSqueezeActual, Mzk1G1PsiCauchyBound3Actual,
Mzk1G1PsiB3AlgPointActual, Mzk1URThetaSourceHullOActual, Mzk1URThetaKJ1SupportActual,
Mzk1URThetaKKummerMassActual, Mzk1ULStepVIIILambdaActual (as written).
2M: Mzk1URThetaKLowerBoundActual (Lead-approved 2026-11-17).

## Addendum 3 (henry O6/M2 recon): ported belyi donors for the analytic h

Importable ported packages (do NOT re-port):
- tmp.external.ported.belyi_poly.TauCeti.FieldTheory.Minpoly.BelyiReduction:
  TauCeti.exists_polynomial_aeval_mem_range [PerfectField F] {K} [Field K] [Algebra F K]:
  finite algebraic set S and roots of q' are sent into F by q (q' != 0);
  TauCeti.exists_forall_dvd_sub_C: q is constant mod each p in P and each irreducible factor of q';
  TauCeti.exists_irreducible_finset_dvd_comp: degree descent step (lex measure
  (max degree, count), minpoly finite set = Galois closure).
- tmp.external.ported.belyi_poly.TauCeti.Algebra.Polynomial.CriticalValues:
  Polynomial.criticalValues, mem_criticalValues_self_iff, criticalValues_comp_subset.
- tmp.external.ported.belyi_poly.TauCeti.Algebra.Polynomial.Belyi:
  TauCeti.belyiPolynomial, criticalValues_belyiPolynomial_subset (criticalValues subset {0,1}).
Remaining gap: these give values into Q / critical values into Q; M2AnalyticTarget needs subset
{0,1} plus q(0) not in {0,1}. The final pin uses the old Lemma 2.4 corpus
(Mzk1Rational24TargetBottomActual, Mzk1BetaAvoidingBelyiRationalActual,
Mzk1Lemma22FullShapeHelpersActual.critValues_comp_subset) or kurt's recursive composition.
henry's Mzk1G1PsiM2AnalyticAssemblyActual (m2AnalyticTarget_of_witness / branchFixedFinite_*) is
the assembly interface. kurt M2 plan: import ported belyi_poly + assembly, prove
m2AnalyticTarget_of_branch by lex induction on the branch minpolys, pinning critical values to
{0,1} via belyiPolynomial/comp composition and avoiding 0 via beta-avoiding step.

## Addendum 4 (2026-11-17 22:05Z, Lead ruling (a)): S_ar is the Fmod-layer quantity

Ruling: S_ar for C3/hstepVIII/D1-hlarge is the Fmod-layer quantity
  SAr_tripodal_Fmod := logDifferentF T.arithmetic.Fmod + logConductorFActual T
(david Mzk1ULSArFmodActual), NOT the F-layer logDifferentF + logConductorFActual.
Reason: paper L1572 log s^Q <= 2 d_mod (log d_Ftpd + log f_Ftpd) + log(2*3*5*l) with Ftpd = Fmod
(Legendre case), and the F-layer version carries an extra [F:Fmod] factor which D4 constants
cannot absorb (david calibration audit: the F/Fmod discriminant term is NOT <= 21).
Consequences for kurt lane:
* kurt C3_upper_route_* keeps S_ar as an abstract real parameter; instantiate it with
  SAr_tripodal_Fmod (no change to the terminal theorems, only the eventual instance);
* hbad_fmod (david) gives Sum_{q,d support} log p <= 2 d_mod S_ar with the Fmod-layer support;
* hstepVIII's S_ar slot likewise uses the Fmod-layer value;
* hlogK tower identity stays F -> K (logDifferentK_sub_logDifferentF_eq, F layer) and is
  independent of the S_ar slot.
Also recorded: logConductorFActual is only Sum_bad log p when bad p is unramified in F; the exact
form is (1/d_mod)*Sum_{qSupport} log p + ramification corrections for p | special.

## Addendum 5 (2026-11-17 22:2xZ): S_ar = F level; the single remaining C3 input is hbad

Lead final caliber: S_ar := SAr_tripodal (F level) := logDifferentF T.arithmetic.F + logConductorFActual T.
Paper L1411-1425 proves SAr_Ftpd <= SAr_F <= SAr_Ftpd + 21, so the +21 is inside the 46/56 constants of
hii_convert/hconst; no constant change. All C3_upper_route_* keep S_ar abstract, so instantiation is direct.

Route L489-498 lstar log(s<=) bound status (Lead asked): ALREADY CLOSED by DONE donors, no new proof:
* Mzk1UHprimeActual.hprime_paperLstarLogs_le (DONE 00:28:56):
    paperLstarLogs eMod l <= (4/3) * paperEar eMod l etaPrm,
  built from Mzk1UCHpktActual.hprime_paperConstants etaPrm_pos
    (fun eta h => primeCounting_le_four_thirds h) he hl le_rfl (IV Prop1.6 prime count, 4/3 constant);
* Mzk1ULHpktActual.ul_hconst_of_paperConstants (DONE 13:04:14): 2 log l + 56 <= (4/9) paperEar eMod l etaPrm;
* kurt wrappers: Mzk1URThetaKC3UpperTerminalActual.hprime_paper / hconst_paper (code clean, infra-only).

C3 input list now: only hbad (named paper obligation Prop1.3(i) local support / L1555-1572) plus the
routine inputs. hbad final target: Sum_{qNo u dNo} log p <= 2 d_mod S_ar (F level), david
Mzk1ULHbadFLevelActual.hbad_F_trunc in progress; qNo segment closed by hq_noSpecial_of_fiber
(DONE 14:09:29).

## Addendum 6 (2026-11-17 23:3xZ, C2 theta scale/bridge audit): legacy P6 object is F-side

Investigated Lead's suggestion to discharge hvol via the DONE per-b inequality
PaperLevelXiFTargetProofActual.perBQPilotLog_le_perBThetaHullLog.
Findings (exact names):
* perBQPilotLog (PaperLevelXiFTargetProofActual:57) and perBThetaHullLog (:65) live on
  qVFamTensorBlock (places = QVFamTensorCoefficientActual.qVFamTensorPlaces, an F-place family);
* ksThetaHullLog (Mzk1URThetaKSideActual:135) lives on ksBlock (places = ksPlaces, a K-place family,
  ksPlaces = fun _ _ => ksPlace T b);
* actualThetaHullLogRoot (PaperLevelXiFTargetActual:116) = Sum_b nativeBadLocalWeight_b *
  actualLocalHullLog_b with nativeBadLocalWeight = 1/[K_w:Fmod_v] (localCompletionDegree inverse);
  ksThetaHullLogRoot_lam = Sum_b thetaLamWeight_b * ksThetaHullLog_b with
  thetaLamWeight = lamWeight/dModF = [Fmod_v:Q_p]/[Fmod:Q].
=> (i) the two objects live on DIFFERENT tensor blocks (F-side vs K-side completions), so neither
   equality nor a 2l/normalization identity can hold without a completion isomorphism
   (obligation: F_to_K_completion_iso, class-field-theory level);
 (ii) weights differ pointwise, and scales differ (classical Q-scale vs M = Q/(2l));
 (iii) the F-side per-b inequality therefore feeds the F-side P6 story only; the K-side C2 lower
   bound is ksThetaHullLogRoot_lam_lower (DONE 13:54:02), which does not need it.
Consequence: hvol : Sum_b thetaTerm_b <= M_paper_v2 stays a NAMED obligation
(obligation: J1_same_q_fiberLe), correct direction S <= M (Lead ruling), used by
Mzk1URThetaKHP5BridgeActual / Mzk1URThetaKHP5J1BridgeActual neg_MpaperV2_le_thetaLam_of_vol.
david's q-side: per-b requires (1/[K_b:Q_p]) order_sigma = (1/(2l[F:Q])) Sum_{P|b} f_P order_P,
tree has no such identity; david proposes corrected weight w'_b = (1/(2l[F:Q])) (Sum f_P order_P)/c_norm_b
for a definitional delivery; the theta side must use the same w'_b for the C2 combination.

## Addendum 7 (2026-11-18 00:3xZ): R1 root-mass weight caliber = c_P = v_P(q_P)/e_P^abs

Per route section 2.1/section 10 and david R0.1 (coord/ROUTE-ALIGNMENT-20261118.md): the root-mass
composition MUST use c_P := order_c/e_abs = v_P(q_P)/e_P^abs, NOT the raw order v_P.  With the
normalized p-adic norm, localNormOrder p x = -log||x||/log p equals v_P(x)/e_abs automatically, so
  rootNu(r O) = log||r||_p = -(c_P/(2l)) log p,   c_P = localNormOrder p (q_P),
and no extra division by e(P/b) is allowed (double counting).  The raw order v_P stays only in the
full-fiber sums Qb (Mzk1ULR0FullFiberActual.Qb_eq_paper_fullFiber) and M_paper_v2 (= Q/(2l)),
which are unchanged:
  (1/[F:Q]) Sum_P f_P v_P(q_P) = f_b v_b/[Fmod:Q] = ([Fmod_b:Q_p]/[Fmod:Q]) c_P.
kurt R1 implementation note: the R1 file states the mass identity in terms of log||r|| (norm), and
only the final identification with -(c_P/(2l))log p uses localNormOrder q (no /e step).

## Addendum 8 (2026-11-18 18:2xZ, Lead ruling): KHP5Bridge direction is S <= M_paper_v2

Mzk1URThetaKHP5BridgeActual.neg_MpaperV2_le_thetaLam_of_bridge has the correct hypothesis
  hbridge : S <= M_paper_v2,   S := Sum_b thetaLamWeight_b * urCeilC_b * log p_b,
because the DONE per-b/aggregate lower bound ksThetaHullLogRoot_lam_lower gives -S <= theta, hence
-M_paper_v2 <= -S <= theta. The old docstring lines stating the reverse (M <= S) were wrong and are
fixed. Do NOT use the 18d hcoef' (thetaLamWeight*urCeilC >= cPFullFiber/(2l), i.e. S >= M) for this
bridge: that direction belongs to a different and non-viable chase (ceil vs root coefficient), and
was recorded only as a decision artefact (Mzk1URThetaHperBReductionActual docstring).
The q-degree comparison (S <= M) remains the paper-faithful input for the K-side C2 bridge; the
container/L_w path (Mzk1URThetaContainerP5Actual) gives the no-ceil equality version.
