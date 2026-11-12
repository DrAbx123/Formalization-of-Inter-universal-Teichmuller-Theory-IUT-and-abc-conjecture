# A695 FINAL REPORT — IUT 3.12 prerequisites + conditional ABC theorem (project conclusion)

## 0. The project's one-line conclusion (machine-checked)
> Apart from the single explicit arithmetic hypothesis `NatRadicalWeightBound`, the entire IUT 3.12 -> ABC
> chain is verified in Lean 4 with only the three standard axioms
> [propext, Classical.choice, Quot.sound]. The reverse direction (ABC => NatRadicalWeightBound) is NOT
> proved and NOT claimed; the ABC gate is NOT passed; no canonical object was changed.

Top-level theorem: `Mzk1FinalConditionalABCActual.final_conditional_ABC :
NatRadicalWeightBound T eN -> ABCConjecture` (gate trio), plus
`final_theorem_package` = final_3_12 AND (NatRadicalWeightBound -> ABCConjecture) AND scope record.

## 1. What is proved (kernel-closed, tri-axiom)

### Corollary 3.12 (IUT III), requirement level
- Kummer transport/realization, Xi-e containment requirement;
- strict_measure is a THEOREM (1D p-scaling Haar strictness + real product comparison);
- resolved requirement (paper inequality, C_Theta >= -1);
- hqneg discharged in a concrete q-pilot side model (vol{q} < 1 i.e. |log q| > 0);
- final assembly / acceptance final / final conditional certificate.

### Paper comparison region necessity
- canonical triple-dependent scaling; A618 fixed-scaling obstruction;
- Gap1 structural consequences (unbounded region log-volume; impossible inside finite hull);
- final region-necessity audit (4 clean gates).

### Direction correction and inverse scaling
- p-adic multiplication CONTRACTS product Haar log-volume, while the paper's lambda-multiple uses
  inverse powers and INCREASES it;
- B1 singleton null measures; inverse prime/product measure and log laws;
- corrected badPart over distinct rational primes (badPart | N, badPart <= N);
- carrier product law; normalization split; log product arithmetic (log primeFactor = -d log p);
- corrected unit-region log law;
- **Gap1 is a THEOREM** (`Mzk1CorrectedGap1UnconditionalActual`) for the corrected inverse-scaling
  triple-dependent region, under explicit hypotheses: full bad support of a+b+c+1, d_b >= 1, unit >= 0.

### Gap2 and the final conditional reduction
- **Gap2 shape => ABCConjecture is a THEOREM** (`Mzk1CorrectedGap2ToABCActual`);
- **`correctedGap2_iff_arith`**: Gap2 shape <=> pure arithmetic `BadSumWeightBound` (geometry eliminated);
- **one-way tightness** (`Mzk1Gap2ArithmeticTightnessActual`): BadSumWeightBound => ABC;
  correctedGap2Shape => ABC; abstract tightness = Nonempty bridge <=> ABC;
- **`Mzk1BadSumWeightBoundExplicitActual`**: `FinalNamedInput` = `BadSumWeightBoundNat` =
  forall eps>0, exists D, forall ABC triples, sum_b e_b d_b log p_b <= (1+eps)*log rad(a*b*c) + D,
  machine-equivalent to `BadSumWeightBound` via `arithmeticWeight (abcRationalPoint a c) = log (natRadical (a*b*c))`;
- **`Mzk1FinalBoundaryCertificateV2Actual`**: finalBoundaryCertificateV2 with a 7-row tri-state scope record;
- **`Mzk1FinalConditionalABCActual`**: the top-level conditional theorem (this report).

## 2. Honest boundary
- The single remaining named input is `NatRadicalWeightBound` (a pure natural-number arithmetic
  inequality about the radical of abc and the bad-support part of a+b+c+1).
- The reverse direction (ABC => NatRadicalWeightBound) is not proved and not claimed; a precise
  obstruction is recorded (sum_b d_b can exceed 1 so ABC's (1+eps) coefficient cannot absorb it).
- No unconditional proof of ABC is claimed; ABC gate NOT passed.

## 3. Evidence
- `AUDIT_LEDGER.md` A546-A695 (78 entries); `coord/STATE.md`;
- `dag/watchdog/logs/` per-file compiler output with `#print axioms` lines;
- Lean code under `tmp/sheaf/xif/paper/`.

## 4. Next (single remaining task)
Prove `NatRadicalWeightBound`: sum_b e_b d_b log p_b <= (1+eps) log rad(a*b*c) + D(eps).
Everything else in the IUT 3.12 -> ABC reduction is machine-checked.