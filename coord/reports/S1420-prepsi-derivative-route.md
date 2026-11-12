# S1420: preΨₙ separability via the derivative / gcd / Squarefree route

Date: 2026-10-31.  File: `tmp/sheaf/xif/paper/S1420PrePsiDerivativeActual.lean`.
Compile: **EXIT=0**, 0 errors, 0 warnings, 0 `sorry`.
SHA256 of the verified source: `e5ca1ae45fce6961a694440f473438d86d66d68ee1e7145a4d66c86cf548c332`
(source mtime 01:09:35, olean 01:11:14).

## Target

```lean
def S1366GenericOddPreΨSeparableInput : Prop :=
  ∀ (F : Type) [Field F] [CharZero F]
    (W : WeierstrassCurve F) [W.IsElliptic] (n : ℤ),
    ¬ Even n → n ≠ 0 → (W.preΨ n).Separable
```

(S1366PrePsiSeparabilityFix.lean:387.)  This package takes the derivative / gcd /
Squarefree route and never mentions a torsion point, `Nat.card`, the group law, or any
counting argument.  The S1396 counting route (detection + torsion cardinality) is left
untouched.

## What is proved (all unconditional unless noted)

Generic polynomial algebra:

* `separable_iff_aeval_derivative_ne_zero`: over any field, `p.Separable ↔`
  `∀ x : AlgebraicClosure F, aeval x p = 0 → aeval x p' ≠ 0`.  Mathlib had only the
  forward direction (`Separable.aeval_derivative_ne_zero`); the converse (no double
  root over the closure ⇒ `IsCoprime p p'`) is proved here from
  `nodup_roots_iff_of_splits` + `Polynomial.count_roots` +
  `isRoot_iterate_derivative_of_lt_rootMultiplicity`.
* `isCoprime_derivative_iff_no_common_root`: `IsCoprime p p' ↔` no point of the
  algebraic closure is a common root.
* `squarefree_iff_aeval_derivative_ne_zero`: over a characteristic-zero field,
  `Squarefree p ↔ p'` never vanishes at a root of `p`.

Target reformulations (each an *equivalence*, so nothing is weakened):

* `s1420_generic_iff_isCoprime`: target ↔ `IsCoprime (preΨ n) (derivative (preΨ n))`.
  In Mathlib v4.32.2 `Polynomial.Separable f` **is** `IsCoprime f (derivative f)`
  (`Polynomial.separable_def`), so the gcd form is the target.
* `s1420_generic_iff_bezout`: target ↔ an explicit Bezout certificate
  `∃ a b : F[X], a * preΨ n + b * derivative (preΨ n) = 1`.
* `S1420GenericOddPreΨSquarefree`, `s1420_generic_iff_squarefree`,
  `s1420_squarefree_iff_separable`: in characteristic zero (`PerfectField.ofCharZero`)
  the target is exactly `Squarefree (W.preΨ n)`.

The exact first algebraic lemma:

* `S1420PrePsiDerivativeNonvanishing`: for every elliptic curve over a
  characteristic-zero field and every odd nonzero `n`, no root of `preΨₙ` in
  `AlgebraicClosure F` is a root of `preΨₙ'`.
* `s1420_nonvanishing_iff_generic`: **this is equivalent to the target** (both
  directions proved), so it is the weakest statement on the derivative route that still
  closes the goal.
* `s1420_preΨ_separable_iff_derivative`, `s1420_preΨ_squarefree_iff_derivative`: the
  two criteria specialised to `preΨₙ`.
* `s1420_concreteSeparable_of_nonvanishing`: consumer — the pointwise statement yields
  `S1366PreΨSeparableInput l` for every `l : PrimeGeFive` via the existing S1366
  consumer `s1366GenericInput_to_concrete`.

Unconditional facts about `preΨ` (new):

* `s1420_ΨSq_eq_preΨ_sq`: odd `n` ⇒ `ΨSqₙ = preΨₙ²`.
* `s1420_derivative_ΨSq_eq`: the derivative formula
  `(ΨSqₙ)' = 2 · preΨₙ · preΨₙ'` for odd `n`, over every commutative ring.
* `s1420_derivative_preΨ_ne_zero`: odd `n`, `(n : F) ≠ 0`, `|n| > 2` ⇒
  `preΨₙ' ≠ 0` (degree `(|n|² - 1)/2 ≥ 1`).
* `s1420_aroots_nodup_and_card_of_generic`: *assuming the target*, `preΨₙ` has
  `(|n|² - 1)/2` pairwise distinct roots in the algebraic closure — the exact root
  count, with no counting argument.
* `s1420_nonvanishing_one`, `s1420_nonvanishing_neg_one`: the pointwise statement
  holds at `n = ±1` (`preΨ_{±1} = ±1`).

## What is not proved

`S1366GenericOddPreΨSeparableInput` / `S1420PrePsiDerivativeNonvanishing` is **not**
inhabited.  The remaining mathematics is exactly the simplicity of the roots of
`preΨₙ`, equivalently a Bezout certificate as above.  No `sorry`, no axiom, no
placeholder: `#print axioms` on all 19 declarations reports only
`propext`, `Classical.choice`, `Quot.sound`.

## Consequence for the route

Because `Separable = IsCoprime f f'` is a definition and characteristic-zero fields are
perfect, the derivative/gcd/Squarefree route has **no slack**: any proof of a strictly
weaker-looking gcd statement is already a proof of the target, and vice versa.  In
particular the missing input cannot be obtained from a degree/leading-coefficient
argument (`natDegree_preΨ`, `preΨ_ne_zero` give neither root simplicity nor a
Bezout pair).

## Verification

```
lake env lean -j1 -R D:\lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1420PrePsiDerivativeActual.olean tmp/sheaf/xif/paper/S1420PrePsiDerivativeActual.lean
EXIT=0, 0 errors, 0 warnings
```

* statement_compiles: yes
* proof_body_checked: yes (kernel-checked, no `sorry`)
* kernel_closed: yes (no `sorryAx`; axioms ⊆ {propext, Classical.choice, Quot.sound})
* target_accepted: **no** (target not inhabited)
