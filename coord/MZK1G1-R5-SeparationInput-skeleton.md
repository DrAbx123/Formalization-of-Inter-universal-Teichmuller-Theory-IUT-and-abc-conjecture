# R5 SeparationInput skeleton (alan, 2026-11-18)

## File
tmp/sheaf/xif/paper/Mzk1G1SeparationInputActual.lean
(imports: Mzk1G1ProbeKQpActual, Mzk1G1UniversalMonogenicIntegersActual,
 Mzk1G1UniversalMonogenicOrderActual, Mzk1G1UniversalSeparationBoundActual,
 Mzk1G1DifferentBoundConservativeActual, Mzk1G1UniversalResidueRootGenerationActual)

## Target signature (KQp e<=d taken as an input theorem parameter)

```lean
theorem separationInput_of_differentBound
    (d : Nat)
    (he_d : ∀ (M : IntermediateField ℚ_[p] (PadicAlgCl p)),
      FiniteDimensional ℚ_[p] M → Module.finrank ℚ_[p] M ≤ d →
      logShellRamificationExponent (K := M) (p := p) ≤ Module.finrank ℚ_[p] M)
    (hbase : localDifferentPaperOrder (p := p) (L := ℚ_[p]) = 0) :
    SeparationInput (p := p) d (d * (d + 2))
```

Actually he_d is expected from Mzk1G1ProbeKQpActual.logShellRamificationExponent_le_finrank_KQp
(instantiated at L := M with the IFNormed instances), so the final signature should be
unconditional except for hbase (single documented prerequisite, route 7.1(3) OPEN).

## Per-M construction

Given M with m = finrank Q_p M <= d:

1. IFNormed gives NormedField/CompleteSpace/NormedAlgebra for `↥M`.
2. nonempty_monogenicIntegers (Mzk1G1UniversalMonogenicIntegersActual) gives
   Mmono : MonogenicIntegers (p:=p) (L:=M), with x : Integers M.
3. let xC : PadicAlgCl p := (Mmono.x : M) coerced to the closure.
   f := minpoly ℤ_[p] Mmono.x (in ℤ_[p][X]); mapped fQ := f.map (algebraMap ℤ_[p] ℚ_[p]).
   - monic: minpoly.monic
   - natDegree = m: IntermediateField.adjoin.finrank + MonogenicIntegers.adjoin_top_rat
   - xC root: minpoly.aeval + coe map
   - |xC| <= 1: x : Integers M has norm <= 1
   - M = adjoin{Q_p}{xC}: MonogenicIntegers.adjoin_top_rat
4. derivative lower bound from MonogenicOrder.localDifferentOrder_eq_addVal_derivative_of_monogenic
   + localDifferentPaperOrder_le_padicVal_succ (base hbase) + B=d(d+2)
   + norm_differentGenerator_eq_prime_rpow_neg_paperOrder (Mzk1DifferentDictionaryActual)
   gives ||f'(xC)|| >= p^{-B}.
5. conjugate separation: fQ splits over PadicAlgCl, roots have norm <=1 (all integral),
   separation_of_derivative_norm_ge gives p^{-B} <= ||xC - y|| for roots y != xC.
6. bundle into SeparationInput d (d*(d+2)).

## Current blockers
- KQp (e<=d) file is queued; he_d can be passed explicitly meanwhile.
- hbase base_different_top: route 7.1(3) OPEN (single documented prerequisite).
- The minpoly/coercion bridge (step 3) is the main Lean work left; no dependency on Serre.
