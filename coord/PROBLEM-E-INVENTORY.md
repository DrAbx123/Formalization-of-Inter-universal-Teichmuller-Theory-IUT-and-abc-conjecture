# PROBLEM E — ASSET INVENTORY (mainline/李维, event-level; Lead A398)

Scope: Problem E = IUT IV §1 / deep inputs row of the gate: AbsTopIII05, H5 O^x, H7/Ob9, EtTh realization deeper rows, uniform height-vs-volume inputs. Citable standard: fresh EXIT0 + checker probe_ok. No audit chain.

## 1. AbsTopIII05 (deep named construction)
- File: tmp/sheaf/xif/paper/AbsTopIII05ReconstructionInputsActual.lean (3685B): `structure DeepInput`, `def absTopIIIDeepInputs : List DeepInput` (4 items), `absTopIIIDeepInputs_length = 4`, `absTopIIIDeepInputs_none_proved` (registers all four as NOT proved).
- Status: CLASS-B NAMED / NOT PROVED (gate L6 deep input).
- Other assets: AbsTopIII01LogShell (log-shell), AbsTopIII07/08/09 (green modules), AbsTopIII10StatementLedger, AbsTopIII11IndexIds, AbsTopIII12AssetMap; hull probes.
- Consumer: IUT IV §1 display / Cor 3.12 assembly (L8 frozen); Hull07/Hull11 interfaces.
- Immediate small task: refine DeepInput fields to precise Prop with paper line refs; expose consumer interface (currently list of strings); no proof attempt until user opts.
- A402/PR-DONE (qpilot, hull-verified): tmp/sheaf/xif/paper/AbsTopIII05RefinedActual.lean (10562B; EXIT0 results:208626 SIZE=10562; checker CITABLE 16 decls probe_ok; probe _S3233AbsTopIII05Probe 208651; sha 08816FDE): D1 Prop58iLocalFieldReconstruction / D2 Prop58iiLogShellReconstruction / D3 Cor55LogFrobeniusCompatibility (bridgeAnchor discharged via sourceLogShellCalibration_invariantImageIdentification) / D4 OrientedGraphAnabelianData (zActionAnchor discharged via chainTranslation_graphAut) / RefinedDeepInputs(K1 K2) / refinedDeepInputKinds_eq_original linkage; S3171RouteSlot + s3171RouteSlot_display_and_abc + absTopIII05Refined_with_s3171RouteSlot; 4 consumption rows + 4 status rows. Remaining named deep anabelian content: Prop 5.8(i)(ii), Cor 5.5 global/panalocal, Section-0 combinatorial data; no port action (TauCeti/Mathlib grep 0).

## 2. H5 O^x (q-side stabilization) + Det/Tensor bookkeeping
- Files: Hull09H5GapsActual.lean (5405B): `hull09_scalingUnits_subset_hull`, `hull09_hull_eq_closure`, `hull09DetTensorBookkeeping_exponent`, `hull09_ray_mem_iff` (PROVED framing of hull/volume inequalities); Hull06DetTensorActual (Det/Tensor bookkeeping); Hull09 rows.
- Status: PARTIAL — H5 GAP reduced to class-B named O^x stabilization (gate L6: H1-H5 closed w/ class-B leftovers); det/tensor bookkeeping PROVED.
- Consumer: thm110 log-volume/height comparison (L8); Hull11/Hull13.
- Immediate small task: integrate hull09_ray_mem_iff + det bookkeeping into Hull11/Hull13 consumer hypotheses list (replace string-level rows with typed Props).
- A398 assembly (DONE): tmp/sheaf/xif/paper/Mzk1HullEInputsActual.lean (8093B; EXIT0 results:208188; checker CITABLE 9 decls, probe _Mzk1HullEInputsProbeActual 208209 probe_ok): `HullEH5NamedInputs` (oInverseNormalization / hull_le_image_volume, class-B explicit params), `HullEH5ProvedComponents` (Hull09 four PROVED components consumed), `hullE_h5_proved_components`.

## 3. H7 / Ob9 (arbitrary-iterate bound)
- Files: Hull08Ob9LogLinkActual.lean (5921B): `structure HullOb9Inputs`, `hull_ob9_interface`, `hull_ob9_repClass_congr` (PROVED interface/rep-class congruence); Hull12Ob9BoundTransferActual.lean (4453B): `hull12_upperBound_transfer`, `hull12_upperBound_transfer_base` (ONE-SIDED bound transfer PROVED); Hull13H7Ob9ComparisonConsumerActual.lean (4543B): `structure HullH7Ob9ComparisonInputs`, `hull13_h7ob9_comparison` (consumes Hull10 + Indet06 + S3182; Cor312 conclusion AND one-sided base bound transfer).
- Status: PARTIAL — one-sided transfer/interface PROVED; full H7 arbitrary-iterate bound remains DEEP CLASS-B NAMED (gate L6).
- Consumer: L8 IUT IV §1 display (frozen); thm110.
- Immediate small task: replace HullH7Ob9ComparisonInputs fields with typed Props linked to Hull08 interface; expose both-sided bound as named Prop with exact paper line; record one-sided vs both-sided gap.
- A402 DONE (two-sided conditional): tmp/sheaf/xif/paper/Hull13TwoSidedBoundActual.lean (5260B; EXIT0 results:208364; checker CITABLE 5, probe 208464): `HullH7Ob9TwoSidedInputs` (comparison + explicit lowerBound/lower_bound_at_iterate), `hull13_twoSided_bound` (Cor312 + base upper bound + two-sided at iterate), `hull13_twoSided_upper_projection`; both-sided transfer to base stays deep Ob9 named.
- A398 assembly (DONE): `HullEH7NamedInput` (arbitraryIterateIndependence, deep Ob9 class-B explicit param); `HullEGenEllIntermediateConclusion` + `hullE_genEll_intermediate` (conditional; consumes Hull10 wiring, Hull12 transfer, Hull13 comparison PROVED chain) and `hullE_cor312` (Cor312HullDetConclusion for Cor312->ABC conditional interface); 10-row inventory `hullEInputRows` (H5 proved 4 / named 2; H7 proved 3 / named deep Ob9 1).

## 4. EtTh realization deeper rows
- Files (all PROVED): EtTh11ThetaRealizationRowsActual.lean (4337B): `etTh11_thetaPowerKernel_mono`, `etTh11_ellipticPowerKernel_mono`, `etTh11_modLThetaProjection_surjective`, `etTh11_modLThetaToElliptic_surjective`; EtTh12ThetaQuotientKernelRowsActual.lean (3742B): `etTh12_thetaToElliptic_eq_map`, `etTh12_thetaToElliptic_mk'`, `etTh12_thetaCenter_eq_ker`, `etTh12_thetaCommutatorKernel_le_derived`, `etTh12_thetaCenter_le_center`; EtTh13ModLFactorizationActual.lean (3645B): `etTh13_modLThetaFactor_comp`, `etTh13_modLEllipticFactor_comp`; plus EtTh07/08/09/10 green modules.
- Status: PROVED rows (power-kernel monotonicity, quotient/kernel, mod-L factorization). Remaining gate-deeper realization rows (scheme-level realization/corollary rows) are class-B named per gate L7.
- Consumer: L7 EtTh route (frozen top), L8.
- Immediate small task: enumerate which EtTh11/12/13 theorems feed the L8 route (typed consumer file), mark scheme-level realization rows named with paper lines.

## 5. IUT IV §1 uniform height-vs-volume inputs
- Files: S3171IUTIVSection1StatementActual (4742B), S3171IUTIVSection1EstimatesActual (2879B), S3171IUTIVSection1InputsActual (3351B), S3171IUTIVSection1DisplayActual (6921B), S3171UniformHeightConsumerActual (4449B), S3171AuditIUTIVSection1 (1450B), S3171IdsActual (2934B).
- Status: statement/estimates/display/consumer layers citable (conditional); uniform height-vs-volume input (b) and region-relative-to-hull/weight inputs remain CLASS-B NAMED (L8 FROZEN).
- Consumer: IUT IV §1 display / Cor 3.12 (frozen); thm110.
- Immediate small task: turn S3171 inputs into typed Prop list with paper lines; add exact statement of uniform height-vs-volume; connect UniformHeightConsumer to Hull11/13 hypotheses.

## 6. H6 (GeometricCore) — mostly resolved, wiring remains
- PROVED/VERIFIED: Mzk1GeometricCorePreciseActual 7 decls 4025B F19EEEC7 probe_ok (MapsTToZero/UnramifiedOverZero:=LevelSetsGenericallyEtale/PullbackIsoDegree; precise witness schema); Mzk1GeomCorePreciseToOldActual 9 decls 7043B 1FA662D1 probe_ok (toOldWitness/toOldRecast; H6 toOld DISCHARGED); GenEll15GeometricCoreAssemblyActual (genEll15_recast_iff/of_data/of_witness PROVED); GenEll10bH6Mzk1WiringActual (h6_genEll_transfer_of_mzk1, mzk1_thm25_of_core, h6_mzk1_interface PROVED conditional).
- Remaining: GenEll15GeometricCoreStatementPrecise named class-B existence; H6 gate layer PARTIAL (wiring/reduction named; no closure).
- Immediate small task: replace Hull11H6Mzk1Upgrade inputs by precise witness (now available) and prove hull11_h6_upgrade from GenEll15 precise statement; record GenEll15 precise existence as class-B named with paper line.
- A402 DONE: tmp/sheaf/xif/paper/Hull11PreciseConsumerActual.lean (5862B; EXIT0 results:208471; checker CITABLE 6, probe _Hull11PreciseProbeActual 208546 probe_ok; sha D0C2250A): `HullH6PreciseUpgradeInputs` (hcore : Mzk1GeometricCoreRecastPrecise), `toOldInputs` (via Mzk1GeomCorePreciseToOldActual.toOldRecast), `hull11_h6_upgrade_precise` (Cor312 + H6 GenEll transfer + Thm2.5 witness conclusion), `hull11_precise_witness_nonempty`; remaining named = 2.2 shape / 2.4 shape / precise GeometricCore existence.

## 7. GenEll 2.1 consumer
- Files: GenEll05Theorem21Actual (4397B): `CaseI`, `CaseII`, `theorem21_i_implies_ii` PROVED, `paper_epsilon_absorption`, `structure Theorem21ReductionInputs` (contains mzk1NoncriticalBelyi field; precise schema).
- Status: (i)=>(ii) PROVED; (ii)=>(i) needs corrected 2.4 conditional wiring (rational F=Q + named Qbar layer) -> currently EXACT PAPER-INPUT.
- Immediate small task: instantiate `Theorem21ReductionInputs` with F=Q RationalGate target (conditional on BetaAvoidingBelyiBaseInput) and record conditional GenEll Thm2.1 (ii)=>(i) consumer row; no closure.

## 8. Asset counts / files touched
- AbsTopIII: 142 files incl. probe/audit; main named = AbsTopIII05ReconstructionInputs; refined = AbsTopIII05RefinedActual (CITABLE 16).
- H5/O^x: 29 files (Hull06, Hull09, Mzk1HullEInputsActual, Indet01/03).
- Ob9: 21 files (Hull08/10/12/13, Hull13TwoSidedBoundActual, Indet06, EtTh09Status).
- EtTh 07-13: ~50 files; realization rows EtTh11/12/13 PROVED.
- IUT IV §1: 13 S3171* files + 49 files mentioning IUTIVSection (consumer graph).

## 9. Suggested immediate small tasks (order)
1. GenEll05 Thm2.1 (ii)=>(i) conditional consumer (instantiate Theorem21ReductionInputs with RationalGate; 1 file; no new math).
2. Hull11 upgrade from precise H6 witness (replace named reduction inputs; use toOld + GenEll15 recast).
3. Typed Props for S3171 inputs (uniform height-vs-volume, region-relative) with paper lines; wire UniformHeightConsumer.
4. Typed Props for Hull13 inputs (both-sided bound) + record one-sided gap.
5. AbsTopIII05 DeepInput precise fields + consumer interface.

## 10. Rules
- GATE NOT PASSED; binding HOLD; L8 FROZEN; no closure claims for paper IV §1; registry 14041; no un-HOLD; event-level records only.

## 11. E-7 UPDATE (mainline A401; fresh-verified support files)
- `Mzk1P1ConsumerDeepInputsActual` CITABLE 11/8734B sha 10CAC8F2 probe_ok: ProblemDDeepInputs + ProblemEDeepInputs as explicit fields of P1CompositeConsumerInputsDeep; deep conditional statements PROVED from F=Q chain (antecedents not asserted); 11-row consumed-vs-named distinction.
- `Mzk1HullEInputsActual` CITABLE 9/8093B sha 2DC5ABD3 probe_ok: HullEH5NamedInputs/HullEH7NamedInput explicit class-B params; HullEH5ProvedComponents (Hull09 reuse); hullE_genEll_intermediate conditional GenEll Cor312->ABC interface (consumes Hull13/Hull12/Hull09); hullE_cor312; 10-row inventory (H5 proved 4/named 2; H7 proved 3/named deep Ob9 1).
- Named blockers recorded: H5 full O(-)^{-1} normalization; hull<=image-volume inequality; deep Ob9 arbitrary-iterate independence; line-bundle iso psi^*O(1)~=O(D).


## 12. E-6/E-3 UPDATE (mainline A405; fresh-verified)
- `Hull11PreciseConsumerActual` CITABLE 6/5862B sha D0C2250A probe_ok: HullH6PreciseUpgradeInputs / toOldInputs / hull11_h6_upgrade_precise / hull11_precise_witness_nonempty (precise H6 witness consumed; upgrade from named reduction inputs).
- `Hull13TwoSidedBoundActual` CITABLE 5/5260B sha 79F714C0 probe_ok: HullH7Ob9TwoSidedInputs / hull13_twoSided_bound / hull13_twoSided_upper_projection (both-sided transfer remains named deep Ob9; projection into one-sided proved chain).
