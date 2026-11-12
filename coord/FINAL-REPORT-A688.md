# A688 FINAL REPORT — IUT 3.12 prerequisites + Gap1 theoremized + ABC boundary (session 2026-11-10/11)

## 1. Proved and kernel-checked (axioms = [propext, Classical.choice, Quot.sound])

### Corollary 3.12 (IUT III) requirement level
- `Mzk1KummerTransportActual`: realized q-pilot image; no completion-valued transport (S342 obstruction).
- `Mzk1KummerRealizationActual`, `Mzk1XiEContainmentRequirementActual`.
- `Mzk1HaarScalingOneDimActual` + `Mzk1HaarStrictScalingProductActual` + `Mzk1HaarStrictChainSummaryActual`: strict_measure is a THEOREM (1D p-scaling Haar strictness + real product comparison).
- `Mzk1Cor312RequirementResolvedActual`: resolvedCor312 / paper inequality / C_Θ ≥ -1.
- `Mzk1HqnegHullModelActual` + `Mzk1Cor312HqnegDischargedActual`: hqneg discharged in a concrete q-pilot side model (vol{q} < 1, i.e. |log q| > 0).
- `Mzk1Cor312FinalAssemblyActual` -> `Mzk1Cor312AcceptanceFinalActual` -> final conditional certificate.

### Paper comparison region necessity (machine-checked)
- canonical triple-dependent scaling (`Mzk1PaperComparisonRegionScalingActual`, `tripleScale = (a+b+c+1) • x`);
- A618 fixed-scaling obstruction (`Mzk1A618ScalingObstructionActual`);
- Gap1 structural consequences (`Mzk1GapStructuralConsequencesActual`);
- final region-necessity audit (`Mzk1PaperRegionNecessityFinalActual`, 4 clean gates).

### Direction correction and inverse scaling (new, A653-A677)
- p-adic multiplication CONTRACTS the product Haar log-volume; the paper's lambda-multiple uses inverse powers and INCREASES it.
- `Mzk1ProductHaarSingletonActual` (B1): singleton null measures.
- `Mzk1ScalingDirectionActual` (hull): 1D inverse prime scaling + `badInvScale_measure` / `badInvScale_measure_toReal` / `badInvScale_log_measure`.
- `Mzk1CarrierBadInvScaleLawActual/ProductActual` (mainline): coordinatewise inverse bad-prime scaling and product Haar law.
- `Mzk1CorrectedLogLawB2Actual` (normalization split), `Mzk1CorrectedLogLawB3Actual` (log product arithmetic, `log primeFactor = -d log p`).
- `Mzk1CorrectedRegionLogLawProvedActual`: unit-region corrected log law.
- `Mzk1CorrectedRegionGap1Actual`: conditional Gap1 (arithmetic core `log c <= sum e_b d_b log p_b`).
- **`Mzk1CorrectedGap1UnconditionalActual`**: Gap1 is a THEOREM for the corrected inverse-scaling triple-dependent region, under explicit hypotheses: full bad support of a+b+c+1, `d_b >= 1`, unit region nonneg. Gates trio.

### Gap2 arithmetic and final boundary
- `Mzk1CorrectedGap2ToABCActual`: Gap2 shape => ABCConjecture is a THEOREM (trio): `log c <= log N <= sum e d log p <= correctedRegionVol <= (1+eps)weight + hull + D`.
- `Mzk1Gap2ArithmeticReductionActual`: `correctedGap2_iff_arith` (Gap2 shape <=> pure arithmetic `BadSumWeightBound`), `logN_le_log_c_add_log3`, `correctedGap2_reduces_to_radical`. Gates trio.
- **`Mzk1FinalBoundaryCertificateV2Actual`**: `finalBoundaryCertificateV2` gate trio. Content: final_3_12; corrected Gap1 theorem; Gap2=>ABC theorem; region-necessity audit; bridge calibration `Nonempty bridge <=> ABC`; scope row: the only remaining named input is the corrected-region Gap2 shape; ABC gate NOT passed; no canonical change.

## 2. The honest boundary
- Cor 3.12 requirement-level chain: fully green and axiom-clean.
- Gap1 (IUT IV Thm 1.10 height estimate): machine-proved THEOREM in the corrected inverse-scaling model under explicit arithmetic hypotheses (full bad support, d_b >= 1, unit >= 0).
- Gap2 shape => ABC: machine-proved THEOREM.
- The ONLY remaining named input is the corrected-region Gap2 shape, machine-equivalent to the pure arithmetic inequality `BadSumWeightBound`: sum_b e_b d_b log p_b <= (1+eps) * arithmeticWeight + D', where `arithmeticWeight (abcRationalPoint a c) = log rad(abc)` (RationalPrimeSupport).
- The abstract boundary calibration `Nonempty Cor312ToABCBridgeInterface <=> ABCConjecture` remains the rigorous tightness statement. The object-level converse (ABC => Gap2) is NOT proved and NOT asserted (it needs extra hypotheses such as d_b = 1 with distinct bad primes, or sum_b d_b <= 1+eps).
- ABC gate NOT passed. No unconditional proof of ABC is claimed.

## 3. Evidence
- `AUDIT_LEDGER.md` A546-A688 (72 entries), `coord/STATE.md`;
- `dag/watchdog/logs/` per-file compiler output with `#print axioms` lines;
- code under `tmp/sheaf/xif/paper/`.

## 4. Next steps
Prove `BadSumWeightBound`: the radical bad-sum inequality sum_b e_b d_b log p_b <= (1+eps) log rad(abc) + D'. This is the single remaining arithmetic input; everything else in the reduction is machine-checked.