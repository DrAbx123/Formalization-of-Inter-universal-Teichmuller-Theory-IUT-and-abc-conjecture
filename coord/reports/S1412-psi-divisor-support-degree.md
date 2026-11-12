# S1412: `ψₙ` divisor identity — support and degree parts

Date: 2026-10-31.

File: `tmp/sheaf/xif/paper/S1412PsiDivisorActual.lean`

- SHA256: `37B4A6BAFF8239E70C29697026A76834F911881924483A6FEA98D0682D1726EA`
- Lines: 359
- Compile: `lake env lean tmp/sheaf/xif/paper/S1412PsiDivisorActual.lean` -> `EXIT 0`
- No `sorry`, `admit`, `axiom` or `opaque` declarations.
- `#print axioms` for the five main results reports only `propext`, `Classical.choice`, `Quot.sound`.

## Scope

`F` algebraically closed field, `W : WeierstrassCurve.Affine F` elliptic, `n : ℤ` odd,
`(n : F) ≠ 0`.  No characteristic restriction beyond `(n : F) ≠ 0`.

## Constructed divisor

Mathlib has no divisor theory on the coordinate ring of `W`, so the file defines the
finite-support integer divisor of `preΨₙ` directly on `W.Point`:

- at an affine point with abscissa `x`, coefficient equal to `rootMultiplicity x (preΨₙ)` at
  each of the two points `(x, y)` and `(x, negY x y)` (a 2-torsion abscissa contributes twice
  the multiplicity at its unique point);
- at `O`, coefficient `-2 * natDegree (preΨₙ)`.

This is the standard zero-positive divisor `Σ_{T ∈ W[n]} T - n²(O)` once the support and
multiplicity inputs are supplied.  The S1397 orientation `n²(O) - Σ_T T` is its negative.

## Proved

1. `psiDivisor_total`: total coefficient `= 0`, unconditionally in `n`.  This is the degree
   half.  For odd `n` with `(n : F) ≠ 0`, the pole order is `2 * natDegree (preΨₙ) = n² - 1`
   (`two_mul_natDegree_preΨ`).

2. `psiZeroSet_eq_affineTorsion`: conditional on
   - `hdet : ∀ P, n • P = 0 → evalDivisionPolynomialAtPoint n P = 0` (forward detection);
   - a finite `T : Finset W.Point` with `T.card = n.natAbs ^ 2` and
     `P ∈ T ↔ n • P = 0`.
   Then the affine zero set of `preΨₙ` is exactly `T.erase 0` (the affine `n`-torsion).
   The proof counts the two points over each root of `preΨₙ` against the `n² - 1` affine
   torsion points; separability is not assumed.

3. `psiDivisor_support_degree`: packages (1), (2), the degree identity
   `total = #T - n²`, and the affine zero characterization
   `P ∈ psiZeroSet ↔ P ≠ 0 ∧ evalDivisionPolynomialAtPoint n P = 0`.

4. `psiZeroCriterion_of_detection_and_card`: from the same two inputs, the support identity
   yields the conditional full zero criterion
   `∀ P, n • P = 0 ↔ evalDivisionPolynomialAtPoint n P = 0`.
   This is the divisor route, not an independent `ψₙ(P) = 0 → n • P = 0` computation, and
   it remains conditional on `hdet` and the torsion cardinality.

## Exact boundary

- Forward detection `hdet` is not proved here for general odd `n`; the tree has it only for
  `n = 2, 3`.
- The finite torsion set `T` of cardinality `n²` is not constructed here; it is the exact
  cardinality input (e.g. the `TorsionCardinalityAt` shape of S1395).
- The reverse direction is not assumed anywhere; it is a consequence of the support identity
  in item 4.
- No unconditional general zero criterion, separability theorem, or torsion cardinality is
  claimed.
