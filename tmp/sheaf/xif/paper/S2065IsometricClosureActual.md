# S2065: unconditional isometric algebraic-closure equivalence

Layer: **O** (completion integral units / S2046 norm bridge).

## Result

For every rational finite place `place : NumberField.FinitePlace ℚ`,
`S2065ClosureIsometry place : S2056ClosureIsometry place` is constructed
unconditionally.  Its underlying ring equivalence is the
`PadicScalarField place`-algebra equivalence

```
S2065ClosureAlgEquiv place :
  SourceAlgebraicClosure place ≃ₐ[PadicScalarField place]
    AlgebraicClosure ℚ_[completionRationalPrime place]
```

and its norm preservation is

```
S2065ClosureAlgEquiv_norm place x :
  ‖S2065ClosureAlgEquiv place x‖ = ‖x‖ .
```

## Method (actual, not conditional)

`PadicScalarField place = ℚ_[completionRationalPrime place]` definitionally.
`SourceAlgebraicClosure place = AlgebraicClosure (NormalizedCompletion place)`
is an algebraic closure of that same scalar field: `NormalizedCompletion place`
is a finite, hence algebraic, extension of it, and
`sourceAlgebraicClosureIsAlgClosure` supplies algebraic closedness.  Therefore
Mathlib's `IsAlgClosure.equiv` (over the common base field) gives the
`PadicScalarField place`-algebra equivalence above.  Its norm preservation is
`Example36.spectralNorm_algHom_eq`: a `K`-algebra homomorphism between
algebraic extensions of `K` preserves the minimal polynomial, hence the
spectral value and the spectral norm.  Both sides of the norm equality are
spectral norms over the same base field by definition.

No uniqueness of the extension of the p-adic absolute value, and no
base-ring-equivalence norm compatibility, is needed; no missing Mathlib lemma
remains.

## Consumers now unconditional

* `S2065IntegralUnitsEquiv place :
    S2055CompletionIntegralUnits place ≃* S2055QpIntegralUnits place`
* `S2065IntegralUnitsIdentification place :
    Nonempty (S2055IntegralUnitsIdentificationRequired place)`
* for `v : FinitePrimePlace 2 7`,
  `S2065NormBridgeOf v : S2046NormBridge v`
  and `S2065NormBridgeOf_available v : Nonempty (S2046NormBridge v)`.

Consequently `S2057NormBridgeOfIsometry` is no longer conditional, and the
S2040 consumer `s2040NormBridgeOfS2056Isometry` can be applied without an
isometry hypothesis.

## Relation to the S2035/S2058 base-ring route

S2035/S2058 build a ring equivalence with `IsAlgClosure.equivOfEquiv` from a
base-ring equivalence `ℚ_[p] ≃+* NormalizedCompletion place`, and record the
norm preservation of that particular ring equivalence as missing.  The
construction here bypasses that conditional by using the common
`PadicScalarField place`-algebra structure directly.  It does not assert
that the two ring equivalences coincide; it supplies one ring equivalence
together with its isometry property, which is exactly what
`S2056ClosureIsometry` requires.

## Verification

* command: `lake env lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S2065IsometricClosureActual.olean tmp/sheaf/xif/paper/S2065IsometricClosureActual.lean`
* `LEAN_EXIT=0` (89.7 s)
* source SHA256 `42151D0F0464A2E14F1F729582DC9B0E58F06DE6D40C4F49F611BB126B67C124`
* olean SHA256 `A37D14DDD07A4EE258AA74E49CAFBB5D69877A25D856B33CC7DD5AF49FFF717F`
* all `#print axioms` results: `propext, Classical.choice, Quot.sound`
* no `sorry`, `admit`, new axiom, empty type, arbitrary inhabitant or
  `Nonempty` gate.
