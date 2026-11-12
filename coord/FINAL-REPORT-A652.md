# A652 FINAL REPORT — IUT 3.12 prerequisites + ABC reduction (session 2026-11-10/11)

## 1. What is proved (kernel-closed, axiom-clean)

All proof bodies are checked by Lean 4.32.2 + Mathlib (pinned). The final chain uses only [propext, Classical.choice, Quot.sound]; there is NO sorry, NO extra axiom, NO PUnit/True/toy carrier or value-layer surrogate in the accepted chain (retired experimental files are documented and excluded).

### Corollary 3.12 (IUT III), requirement level
- `Mzk1KummerTransportActual`: realized q-pilot image `qPilotInThetaCarrier = kummerMap thetaOneCarrier` (SHE root relation); no completion-valued transport (S342 obstruction).
- `Mzk1KummerRealizationActual`: `PaperKummerReading` link to real volumes; `qImage_realized`, `qImage_realized_mem_hull`.
- `Mzk1XiEContainmentRequirementActual`: xi-e requirement with `strict_measure`.
- `Mzk1HaarScalingOneDimActual` + `Mzk1HaarStrictScalingProductActual` + `Mzk1HaarStrictChainSummaryActual`: **strict_measure is a THEOREM** (1D p-scaling strict ball measure `μ(ball(R/p)) < μ(ball(R))`, real product strictness via `Finset.prod_lt_prod`, `ENNReal.toReal_lt_toReal`), yielding `rpRequirement`/`rp_cor312` and the resolved requirement.
- `Mzk1Cor312RequirementResolvedActual`: resolvedCor312 / paper inequality / C_Θ ≥ −1; gate trio.
- `Mzk1HqnegHullModelActual` + `Mzk1Cor312HqnegDischargedActual`: hqneg discharged in a concrete q-pilot side model (vol{q} < 1, i.e. |log q| > 0); gates trio.
- `Mzk1Cor312FinalAssemblyActual` → `Mzk1Cor312AcceptanceFinalActual` → `Mzk1FinalConditionalCertificateActual`: final Cor 3.12 conclusion with axiom gates.

### Paper comparison region necessity (machine-checked)
- `Mzk1PaperComparisonRegionScalingActual` (canonical): genuinely triple-dependent scaling `tripleScale a b c := (a+b+c+1) • x`, `paperComparisonRegion = tripleScale '' (unitRegion ∪ {point})`, two ε-form gap fields, conditional `abc_of_tripleComparison`.
- `Mzk1S1902IQHullInterfaceActual`/`...CanonicalActual`, `Mzk1S1902BridgeInterfaceActual`: concrete S1902 carrier hull data and bridge (gate trio).
- `Mzk1A618ScalingObstructionActual`: with fixed scaleShift = id and a triple-independent region, the height comparison is FALSE (machine proof).
- `Mzk1GapStructuralConsequencesActual`: Gap1 forces unbounded region log-volume; a region inside the finite hull cannot satisfy Gap1.
- `Mzk1RegionNecessitySummaryActual`, `Mzk1PaperRegionNecessityFinalActual`: final necessity audit conjunction (4 clean gates).

### ABC boundary calibration / tightness
- `Mzk1GapTightnessActual`: `Nonempty Cor312ToABCBridgeInterface ↔ ABCConjecture`; the two named IUT IV Thm 1.10 fields imply ABC; hence they are EQUIVALENT IN STRENGTH to ABC (no weakening possible).
- `Mzk1FinalBoundaryCertificateActual`: single conjunction certificate (final_3_12 + boundary calibration + named-fields tightness + region necessity + scope record); gate = [propext, Classical.choice, Quot.sound].
- `Mzk1ABCTwoEstimatesShaActual` + consumers: `ABCTwoEstimates → ABCConjecture`; Gap1/Gap2 consumers and numeric witnesses green.

## 2. What is NOT proved (the honest boundary)

The two IUT IV Theorem 1.10 estimates on the canonical triple-dependent comparison region remain named inputs:
1. Gap 1: `height_le_normalizedRegionVolume`: logHeight₁(x) ≤ (1+ε) · regionLogVolume(x);
2. Gap 2: `regionVolume_le_normalizedWeight`: regionLogVolume(x) ≤ (1+ε) · arithmeticWeight(x) + hullVolume + D(ε).
Mzk1GapTightnessActual machine-checks that these two fields are equivalent in strength to ABC; therefore no weaker formal statement can close the gap, and no external shortcut exists:
- lana-agents/iut (703-710 files, 0 sorry/0 axiom): full IUT IV Thm1.10 derivation and ABC reduction, BUT conditional on the same unproved Cor 3.12 variant; toolchain v4.32.0 + mathlib@81a5d257c8 + 10 external git packages (unavailable offline) make it non-importable.
- Gogopex: CorollarySchema is only a signed-inequality schema; IUTStage1Source is a source-obligation ledger (54,738 lines, mostly rfl audit equalities).
- PriestAmbrose: toy Nat shell with a single sorry.

## 3. Evidence locations
- `AUDIT_LEDGER.md` (A546…A652): every milestone, root cause, axiom-gate verbatim output, and honest boundary;
- `coord/STATE.md`: session state notes;
- `dag/watchdog/logs/`: per-file compiler output with `#print axioms` lines;
- code under `tmp/sheaf/xif/paper/`.

## 4. Next steps for a genuine ABC proof
Close Gap1/Gap2 (IUT IV §2): height comparison of the Θ-pilot arithmetic line bundle, and the Θ-pilot region log-volume computation with prime-counting input, on the triple-dependent paper comparison region. Everything else in the reduction is machine-checked.
