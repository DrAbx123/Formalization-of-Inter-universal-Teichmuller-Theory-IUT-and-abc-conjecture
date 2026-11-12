# S1397: general odd-n division-polynomial zero criterion — exact gap

Date: 2026-10-30. No Lean file written: no in-tree proof route; report only.

## Target

For `W : WeierstrassCurve F`, `n : ℤ` odd, and `P : W.toAffine.Point`:

```lean
W.evalDivisionPolynomialAtPoint n P = 0 → n • P = 0
```

i.e. `W.DivisionPolynomialRootsAreTorsion n` for all odd `n`.

## 1. What is actually proved

S1373 `S1373ZeroCriterionActual.lean`:

- `divisionPolynomialZeroCriterion_two`;
- `three_nsmul_eq_zero_of_evalDivisionPolynomialAtPoint_three_eq_zero`;
- `divisionPolynomialZeroCriterion_three`.

The n=2,3 proofs are actual, every characteristic.

## 2. Why n=3 does not generalize by the same computation

The n=3 proof writes `P = (x,y)`, `A = 3x² + 2a₂x + a₄ - a₁y`,
`B = 2y + a₁x + a₃`, uses the syzygies

```text
Φ₂(x) = A² + a₁AB - (a₂ + 2x)B²
Ψ₂Sq(x) = B²
Ψ₃(x) = xΨ₂Sq(x) - Φ₂(x)
```

and the doubling formula `x(2P) = ... / B²`.  This only reaches `2P = ±P`.
For `n ≥ 5` there is no corresponding one-step formula expressing `nP`
from `ψ_n(x(P))`; the general root criterion is the divisor identity

```text
div(ψ_n) = n²(O) - Σ_{T ∈ W[n]} T
```

or the bivariate division-polynomial group law, neither of which is available.

## 3. Missing Mathlib API

Mathlib v4.32.2 provides:

- univariate `preΨ_n`, `Ψ_n`, `Φ_n`, degree/nonzero lemmas;
- `evalDivisionPolynomialAtPoint` from the tree;
- affine/Jacobian addition formulas.

It does **not** provide:

1. a bivariate division polynomial `Ψ_n(X,Y)` with evaluation law at an
   affine point;
2. the function `ω_n` / the complete bivariate division-polynomial data;
3. divisor theory on the coordinate ring of `W`;
4. a group-law bridge `ψ_n(P) = 0 ↔ n • P = 0` for general `n`.

S1377 ports EllSequence identities (Stange/elliptic nets) but stops at the
sequence layer; it gives no point-evaluation/group-law bridge.  S1378 probes
only compute doubling/addY identities, not the general criterion.

## 4. Exact first lemma

The exact first missing object is the general **bivariate evaluation/divisor
lemma** in one of these equivalent forms:

```lean
-- point-level root criterion
theorem rootsAreTorsion_of_odd
    (n : ℤ) (hodd : ¬ Even n)
    (P : W.toAffine.Point)
    (h : W.evalDivisionPolynomialAtPoint n P = 0) :
    n • P = 0
```

or

```lean
-- divisor identity for ψ_n on W
theorem divisor_divisionPolynomial
    (n : ℤ) (hodd : ¬ Even n) :
    divisor (W.ψ n) = n^2 • (O) - ∑ T ∈ W[n], (T)
```

or the bivariate group-law identity

```lean
theorem eval_ψ_eq_zero_iff_nsmul
    (n : ℤ) (P : W.toAffine.Point) :
    W.ψ n P = 0 ↔ n • P = 0
```

None is in the tree.  S1397 does not fabricate any of them.

## 5. Out of scope

Per the assignment: no separability, no torsion cardinality, no zero
criterion for the concrete Gaussian l, and no Kummer inputs were used.

## 6. Conclusion

- Actual: n=2 and n=3 zero criteria (S1373).
- General odd-n root half is **not proved**; the n=3 doubling argument does
  not extend.
- **Exact first lemma:** general bivariate division-polynomial evaluation /
  divisor identity (root criterion for all odd n), absent from Mathlib 4.32
  and from the local tree.
- No Lean file written to avoid a wrapper around the target; report EXIT=0.
