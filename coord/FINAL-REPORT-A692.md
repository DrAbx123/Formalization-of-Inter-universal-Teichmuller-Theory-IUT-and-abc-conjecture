# A692 FINAL REPORT (supersedes A688) — IUT 3.12 prereqs, Gap1 theorem, ABC boundary with explicit named input

## 0. One-line state
Cor 3.12 requirement chain green; corrected-region Gap1 is a THEOREM; Gap2 => ABC is a THEOREM;
the ONLY remaining named input is `FinalNamedInput` (= `BadSumWeightBoundNat`, a pure natural-number
radical bad-sum inequality); the reverse (ABC => Gap2) is NOT proved nor claimed; ABC gate NOT passed.

## 1. Green and axiom-clean (only [propext, Classical.choice, Quot.sound])

### Corollary 3.12 (IUT III), requirement level
- Kummer transport/realization, Xi-e containment requirement, strict_measure THEOREM (1D p-scaling Haar
  strictness + real product comparison), resolved requirement (paper inequality, C_Theta >= -1),
  hqneg discharged in a concrete q-pilot side model (vol{q} < 1 i.e. |log q| > 0), final assembly,
  acceptance final, final conditional certificate.

### Paper comparison region necessity (machine-checked)
- canonical triple-dependent scaling; A618 fixed-scaling obstruction; Gap1 structural consequences;
  region-necessity final audit (4 clean gates).

### Direction correction and inverse scaling
- p-adic multiplication CONTRACTS product Haar log-volume; the paper lambda-multiple uses inverse powers
  and INCREASES it.
- hull: singleton null measures (B1), inverse prime/product measure and log laws,
  corrected badPart over distinct rational primes with badPart | N and badPart <= N.
- mainline: coordinatewise inverse bad-prime carrier product law; normalization split; log product
  arithmetic (log primeFactor = -d log p).
- corrected unit-region log law; conditional Gap1 (arithmetic core log c <= sum e_b d_b log p_b).
- **`Mzk1CorrectedGap1UnconditionalActual`: Gap1 is a THEOREM** for the corrected inverse-scaling
  triple-dependent region (explicit hypotheses: full bad support of a+b+c+1, d_b >= 1, unit >= 0).

### Gap2 => ABC and final boundary
- **`Mzk1CorrectedGap2ToABCActual`: Gap2 shape => ABCConjecture is a THEOREM.**
- **`Mzk1Gap2ArithmeticReductionActual`: `correctedGap2_iff_arith`** (Gap2 shape <=> pure arithmetic
  `BadSumWeightBound`), `logN_le_log_c_add_log3`, `correctedGap2_reduces_to_radical`.
- **`Mzk1Gap2ArithmeticTightnessActual`: one-way tightness** (`badSumWeightBound_implies_ABC`,
  `correctedGap2Shape_implies_ABC`, `bridge_boundary_calibrated`); reverse NOT proved with explicit
  counter-argument (sum_b d_b can exceed 1 so ABC's (1+eps) cannot absorb it).
- **`Mzk1BadSumWeightBoundExplicitActual`: `FinalNamedInput`** = `BadSumWeightBoundNat` =
  `forall eps>0, exists D, forall abc, sum_b e_b d_b log p_b <= (1+eps)*log rad(a*b*c) + D`,
  equivalent to `BadSumWeightBound` via the green dictionary
  `arithmeticWeight (abcRationalPoint a c) = Real.log (natRadical (a*b*c))`.
- **`Mzk1FinalBoundaryCertificateV2Actual`: `finalBoundaryCertificateV2`** gate trio; scope record is
  a 7-row tri-state table ending with `FinalNamedInput` = NAMED.

## 2. Honest boundary details
- Remaining named input: `FinalNamedInput` only (machine-equivalent to the corrected-region Gap2 shape).
- Reverse direction (ABC => Gap2 / ABC => FinalNamedInput) is NOT proved and NOT asserted.
- The rigorous abstract tightness remains `Nonempty Cor312ToABCBridgeInterface <=> ABCConjecture`.
- No unconditional proof of ABC is claimed; ABC gate NOT passed; no canonical object changed.

## 3. Evidence
- `AUDIT_LEDGER.md` A546-A692 (75 entries); `coord/STATE.md`;
- `dag/watchdog/logs/` per-file compiler output with `#print axioms` lines;
- code under `tmp/sheaf/xif/paper/`.

## 4. Next (single remaining task)
Prove `FinalNamedInput`: the radical bad-sum inequality
`sum_b e_b d_b log p_b <= (1+eps) * log rad(a*b*c) + D(eps)` for all ABC triples.
Everything else in the IUT 3.12 -> ABC reduction is machine-checked.