# separationInput_of_differentBound — statement and dependency plan (alan, 2026-11-17)

## Target statement

For p prime, d B : Nat, with B = differentBound p d (or d*(v_p(d)+2) for the Serre version):

```lean
theorem separationInput_of_differentBound
    (d B : Nat)
    (hB : B = d * (padicValNat p d + 2))
    (hdelta : ∀ M : IntermediateField ℚ_[p] (PadicAlgCl p),
      FiniteDimensional ℚ_[p] M → Module.finrank ℚ_[p] M ≤ d →
      (localDifferentOrder (p := p) (L := M) : ℝ) ≤ (B : ℝ)) :
    SeparationInput (p := p) d B
```

where `SeparationInput d B` is defined in
`Mzk1G1UniversalResidueRootGenerationActual`:
for each finite M with finrank <= d it gives n, f, x with
f monic, natDegree = n, 0 < n, IsIntegral Q_p x, ||x|| <= 1,
finrank Q_p M = n, f.aeval x = 0, M = adjoin{x}, and
for every conjugate y != x: p^(-B) <= ||x - y||.

## Dependency graph (bottom-up)

1. **IFNormed instances** (DONE 00:44:24)
   `Mzk1G1UniversalIFNormedActual`:
   NormedField, IsUltrametricDist, CompleteSpace, NormedAlgebra for `↥M`.

2. **Unconditional monogenic** (DONE 01:07:52)
   `Mzk1G1UniversalMonogenicIntegersActual.nonempty_monogenicIntegers`:
   yields Mmono : MonogenicIntegers (p:=p) (L:=M), hence
   x : Integers M with Algebra.adjoin ℤ_[p] {x} = ⊤ and
   `MonogenicIntegers.adjoin_top_rat` gives Algebra.adjoin ℚ_[p] {x} = ⊤.

3. **Different = derivative ideal** (DONE 23:05:14 conditional file)
   `Mzk1G1UniversalMonogenicLocalActual.localDifferentIdeal_eq_span_derivative_of_monogenic`.

4. **delta = addVal(f')** (pending)
   `Mzk1G1UniversalMonogenicOrderActual.localDifferentOrder_eq_addVal_derivative_of_monogenic`
   with the DVR instance `[IsDiscreteValuationRing (Integers M)]` supplied by
   `integersIsDiscreteValuationRing`.

5. **Serre delta <= B** (pending)
   `Mzk1G1UniversalSerreDeltaBoundActual.localDifferentOrder_lt_logShell_mul`
   plus e <= finrank and hB to get `hdelta` above.

6. **Derivative lower bound -> conjugate separation**
   From addVal f' <= logShell*(v_p(logShell)+2) <= B (in fact delta <= B by hdelta and
   step 4), `||f'(x)|| >= p^(-B)`, then
   `Mzk1G1UniversalSeparationActual.norm_eval_derivative_le_norm_sub` /
   `Mzk1G1UniversalSeparationBoundActual.separation_of_derivative_norm_ge`
   gives `p^(-B) <= ||x - y||` for conjugates y != x.

7. **Assembly of SeparationInput**
   Bundle steps 1-6 for each M: n = finrank Q_p M, f = minpoly ℤ_[p] x,
   root/integrality/monogeneity from MonogenicIntegers, separation from step 6.

## hspecial donor update (2026-11-17 22:43)

The invalid `Mzk1ULSpecialPrimesNumericActual` donor was replaced by
`Mzk1ULSpecialPrimesOwnActual.specialPrimes_log_sum_le_own (l : PrimeGeFive)`
(DONE 2026-11-17T14:42:07Z, three axioms).  F3 uses it through
`Mzk1G1F3HsQInputActual.specialPrimes_log_sum_le_own'`; old
`specialPrimes_log_le` (log30<=5) is kept only as a numeric kernel.

## Current blockers

* SerreDeltaBound: queued (last FAIL was a stale run before the `letI`/valuation fixes;
  current state is no-log = awaiting compile). If the new run fails, read the first error and
  decide code vs infra (OOM/olean reading is infra).
* MonogenicOrder and SeparationToUFLE: queued/being fixed.

## Next actions after OOM cooldown

* one file at a time: MonogenicOrder -> SeparationToUFLE -> SerreDeltaBound -> this file.
