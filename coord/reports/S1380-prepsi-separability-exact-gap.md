# S1380: S1366GenericOddPreΨSeparableInput — exact gap

Date: 2026-10-30. No Lean file written: no actual proof route in-tree; report only.

## Target

```lean
def S1366GenericOddPreΨSeparableInput : Prop :=
  ∀ (F : Type) [Field F] [CharZero F]
    (W : WeierstrassCurve F) [W.IsElliptic] (n : ℤ),
    ¬ Even n → n ≠ 0 → (W.preΨ n).Separable
```

(S1366PrePsiSeparabilityFix:387.)

## 1. Local Mathlib API

Mathlib v4.32.2 in this tree has:

- `WeierstrassCurve.preΨ` definition and recurrence (`preΨ_even`, `preΨ_odd`,
  `preΨ_neg`, `preΨ_zero/one/two/...`);
- degree and leading-coefficient lemmas in `DivisionPolynomial/Degree.lean`
  (`natDegree_preΨ`, `coeff_preΨ_ne_zero`, `preΨ_ne_zero`);
- **no** separability, squarefree, discriminant, or root-count theorem for
  `preΨ`.

A full grep over `.lake/packages/mathlib` for `separable_pre`, `preΨ.*Separable`,
`Separable.*preΨ` returns nothing.

## 2. TauCeti not importable

S1366 header (lines 53-58) records: TauCeti's
`WeierstrassCurve.separable_prePsi` is Lean v4.36.0-rc1 and a newer Mathlib
pin.  This tree is Lean v4.32.2 / Mathlib v4.32.2; TauCeti is not importable
and no local copy exists under `D:\lean`.

Porting requires the actual TauCeti proof body, which is absent locally and
not reachable from this sandbox (GitHub/taucetiproject TCP endpoints are
blocked).  Reconstructing it from scratch would be a separate large
formalization.

## 3. Why degree/root bound alone cannot close it

- `natDegree_preΨ` gives the upper bound `(n^2 - 1)/2`, not distinct roots.
  A degree upper bound only shows there are at most that many roots;
  separability requires counting roots **with multiplicity one**.
- The existing S1366 counting theorem
  `s1366Separable_of_detection_and_card`:
  detection + torsion cardinality ⇒ separability.
  Both inputs are explicitly excluded by the current assignment
  ("不要碰 torsion cardinality/zero criterion"), and are owned by other
  agents.
- Without detection or an equivalent derivative/gcd theorem, the root lower
  bound is exactly what is missing; the degree bound cannot supply it.

## 4. Exact first field

The exact first missing lemma is the TauCeti theorem itself (odd,
characteristic-zero part):

```lean
theorem separable_prePsi
    (W : WeierstrassCurve F) [W.IsElliptic] (n : ℤ)
    (hodd : ¬ Even n) (hn : n ≠ 0) :
    (W.preΨ n).Separable
```

or equivalently a direct algebraic proof of

```lean
(W.preΨ n).Separable ↔ (W.preΨ n).Squarefree
```

with the squarefree statement proved from a derivative/gcd identity for
`preΨ_n` (not present in Mathlib 4.32).

Needed ingredients, none currently in-tree:

1. a derivative formula for `preΨ_n` in terms of division-polynomial data;
2. an algebraic proof that `gcd(preΨ_n, derivative preΨ_n) = 1` for odd n
   in characteristic zero;
3. or the TauCeti detection/cardinality route, which is forbidden here.

## 5. Conclusion

- No actual Lean proof of `S1366GenericOddPreΨSeparableInput` is written.
- TauCeti is unavailable; Mathlib 4.32 has no separability theorem;
  degree/nonzero lemmas are insufficient.
- The existing S1366 proof route requires detection + torsion cardinality,
  explicitly out of scope and owned by other agents.
- **Exact first field:** TauCeti `separable_prePsi` (char-zero odd part), or
  the derivative/gcd squarefree theorem for `preΨ_n`.
- No fake `axiom`/`sorry`/`True` used; report only, EXIT=0.
