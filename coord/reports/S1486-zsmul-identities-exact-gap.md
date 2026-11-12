# S1486: Doubling/Addition identities for smulEval — exact gap

Date: 2026-10-31. No new Lean file: the two identities reduce to the TauCeti
Universal ring identities, which are absent from Mathlib v4.32.2.  Report only.

## Target

From S1472:

```lean
DoublingIdentity W :=
  ∀ x y n,
    Jacobian.dblXYZ W (smulEval W x y n) = smulEval W x y (2 * n)

AdditionIdentity W :=
  ∀ x y n,
    Jacobian.addXYZ W (smulEval W x y n) (smulEval W x y (n + 1)) =
      smulEval W x y (2 * n + 1)
```

with the actual `smulEval` triple using S1410's bivariate `W.ω` and `W.ψ`.

## Actual status

S1472 proves:

- `smulEval_zero`, `smulEval_one`;
- point bridge at `n = 0, 1`;
- no `sorry`/`axiom`.

Neither `DoublingIdentity` nor `AdditionIdentity` is proved in the tree.

## Exact first polynomial identity

TauCeti reduces both identities to universal polynomial identities:

```lean
dblXYZ_smulRing :
  dblXYZ curveRing (smulRing n) = smulRing (2 * n)

addXYZ_smulRing :
  addXYZ curveRing (smulRing m) (smulRing n) =
    AdjoinRoot.mk curve.polynomial (curve.ψ (n - m)) • smulRing (n + m)

addXYZ_smulRing₁ :
  addXYZ curveRing (smulRing n) (smulRing (n + 1)) =
    smulRing (2 * n + 1)
```

Here `curveRing`, `curveField`, `smulRing`, `smulPoly`, `ringEval` are the
TauCeti Universal layer.  Mathlib v4.32.2 has none of these objects:

- no `Universal.Ring`, `Universal.Field`, universal curve;
- no `smulPoly` / `smulRing` (universal `(φₙ,ωₙ,ψₙ)`);
- no `ringEval`/`ringEval_comp_smulRing` specialization homomorphism.

Their definition also needs the bivariate ω defining identity

```text
2 * ω_n + a₁ * φ_n * ψ_n + a₃ * ψ_n ^ 3 = ψc_n
```

whose reduced-invariant proof needs

```text
IsEllipticNet (normEDS b c d)
```

which is an explicit TODO in Mathlib v4.32.2 and is not proved in TauCeti.
S1410 ports the actual ω definition and eval laws but deliberately omits this
identity.

## Second exact field

After the polynomial identities, the induction needs the point-class addition
formula for distinct multiples.  TauCeti uses `Point.add_point_of_ne`
(and `Point.two_zsmul_point`) to obtain the `addXYZ`/`dblXYZ` representative;
Mathlib v4.32.2's Jacobian API has `add_point`, `addMap_eq`, `add_of_eq`,
`add_of_not_equiv`, but no `add_point_of_ne` theorem for distinct Jacobian
points.  This is the second missing API field.

## Conclusion

No new Lean file is written: a file could only restate `DoublingIdentity` /
`AdditionIdentity` or depend on the absent Universal layer.

- Actual: S1472 minimal layer; bivariate ω/eval laws (S1410).
- **Exact first identity:** TauCeti `dblXYZ_smulRing` and
  `addXYZ_smulRing₁` over the Universal curve.
- **Also missing:** `IsEllipticNet (normEDS b c d)` for the ω defining
  identity; `Point.add_point_of_ne` for the induction step.
- No fake axiom/sorry; report EXIT=0.
