# S2804 — EllipticPrimeTorsionCardinality at p=3: support check and first error

Date: 2026-11-07. Check only; no fake finiteness.

## 1. Does the API accept arbitrary prime n?

YES for odd primes.  The signatures are:

```lean
WeierstrassCurve.card_le_of_prime_divisionLocus
  (W : WeierstrassCurve K) {p : ℕ}
  (hp : Nat.Prime p) (hodd : p ≠ 2) (hchar : (p : K) ≠ 0)
  (S : Finset W.toAffine.Point)
  (hS : ∀ P ∈ S, P ≠ 0 ∧ W.evalDivisionPolynomialAtPoint p P = 0) :
  S.card ≤ p ^ 2 - 1

WeierstrassCurve.card_le_of_prime_divisionLocus_with_zero
  ... : S.card ≤ p ^ 2
```

There is no restriction to 5 or to a fixed prime.  p=3 is accepted:
`Nat.Prime 3`, `3 ≠ 2`, and over char 0 `(3 : K) ≠ 0`.

Raw `card_le_of_eval_preΨ_eq_zero` / `card_le_of_evalDivisionPolynomialAtPoint_eq_zero`
also accept any odd n (including 3) with (n : K) ≠ 0.

## 2. Actual 3-torsion bridge

`LeanFormal/IUT/ABCBridge/Galois/EllipticTorsionAlgebraicity.lean` has the actual:

```lean
divisionPolynomialDetectsTorsion_three
  (W : WeierstrassCurve F) [DecidableEq F] :
  W.DivisionPolynomialDetectsTorsion 3
```

So every 3-torsion point is in the 3-division locus.  This is stronger than the
generic bridge interface, which is only a hypothesis.

## 3. FIRST ERROR

The API bounds a **given Finset** of division-locus points.  It does not prove
that the nsmul-torsion subgroup is finite.  Direct attempt:

```lean
example {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic] :
    Finite (AddSubgroup.torsionBy W.toAffine.Point (3 : ℤ)) := inferInstance
```

error:

```text
failed to synthesize instance of type class
  Finite ↥(AddSubgroup.torsionBy W.toAffine.Point 3)
```

So the first missing step is exactly:

1. map a nonzero 3-torsion point to its x-coordinate;
2. its image lies in the finite root set of `preΨ 3` (using the actual bridge);
3. each fiber has at most 2 points (`P` and `-P`);
4. apply `Set.Finite.of_finite_fibers` (Mathlib Data/Set/Finite/Lattice.lean)
   to get `Finite` of the 3-torsion set.

This is a finite-fiber argument, not a new torsion-card theorem.

## 4. Consequence for E[6]

The proposed E[6] decomposition P ↦ (3P, 2P) is injective into E[2] × E[3].
E[2] finiteness is the same kind of two-fiber argument using the 2-division
polynomial (and the actual `divisionPolynomialDetectsTorsion_two`).  Once both
factors are finite, the product is finite and E[6] is finite; then the
coordinate set S2790CoordSet is finite and S2803 finite-dimensionality applies.

No fake `Finite` instance, no fake torsion cardinality.