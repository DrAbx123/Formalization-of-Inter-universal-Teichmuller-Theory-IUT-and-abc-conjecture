# S1472: minimal ZSMul / bivariate omega port

Date: 2026-10-31. New independent Lean file.

## 1. Result

`tmp/sheaf/xif/paper/S1472ZSMulOmegaPortActual.lean`

```text
EXIT=0
SHA256 85ABCF2D58B73D819B058567B48257676EDCA2BAEC368B94CADDF64787C79DBF
olean  .lake/build/lib/lean/tmp/sheaf/xif/paper/S1472ZSMulOmegaPortActual.olean
olean SHA 4732C0CC3763D0EFE7019B1FB88D3E11CC08117772F6E1942824A96BA6AABEA8
size 192960
```

No `sorry`/`axiom`.  `#print axioms` for `smulEval_zero`, `smulEval_one`,
`zsmulEqSmulEvalAt_zero`, `zsmulEqSmulEvalAt_one` is the standard trio.

## 2. Actual layer

Imports the actual bivariate omega from S1410 (`W.ω`, `ω_def`,
`evalEval_ω`) and the Jacobian bridge API from S1411.

```lean
noncomputable def smulEval (W) (x y : F) (n : ℤ) : Fin 3 → F :=
  ![evalEval x y (W.φ n), evalEval x y (W.ω n), evalEval x y (W.ψ n)]
```

Proved actually:

- `smulEval_zero : smulEval W x y 0 = ![1,1,0]`,
- `smulEval_one : smulEval W x y 1 = ![x,y,1]`,
- `zsmulEqSmulEvalAt_zero` and `zsmulEqSmulEvalAt_one`:
  `(n • P).point = ⟦smulEval W x y n⟧` at `n = 0, 1`.

These use the actual `φ_zero/one`, `ψ_zero/one`, and S1410's
`ω_zero/one/evalEval_ω`; no placeholder middle coordinate.

## 3. Exact first fields for the full `zsmul_eq_smulEval`

The full bridge is stated as:

```lean
def ZSMulEqSmulEval (W) : Prop :=
  ∀ (x y : F) (hns : W.Nonsingular x y) (n : ℤ),
    (n • (Point.some x y hns).toJacobian).point = ⟦smulEval W x y n⟧
```

It is not proved.  The first two exact group-law inputs are:

```lean
def DoublingIdentity (W) : Prop :=
  ∀ x y n,
    Jacobian.dblXYZ W (smulEval W x y n) = smulEval W x y (2 * n)

def AdditionIdentity (W) : Prop :=
  ∀ x y n,
    Jacobian.addXYZ W (smulEval W x y n) (smulEval W x y (n + 1)) =
      smulEval W x y (2 * n + 1)
```

TauCeti's proof of these reduces to universal polynomial identities
(`dblXYZ_smulRing`, `addXYZ_smulRing`) on the universal curve/ring, which
Mathlib v4.32.2 does not provide.  The universal `ω` defining identity
(`2ω + a₁φψ + a₃ψ³ = ψ_c`) also needs

```text
IsEllipticNet (normEDS b c d)
```

an explicit TODO in Mathlib v4.32.2 (and not proved in TauCeti itself).
S1410 ports the actual ω definition/evaluation but deliberately omits this
identity.

So the exact first fields are:

1. `DoublingIdentity` / `AdditionIdentity` for the actual `smulEval`;
2. universal curve/ring and polynomial identities `dblXYZ_smulRing`,
   `addXYZ_smulRing`;
3. `IsEllipticNet (normEDS b c d)` (for the ω defining identity),
4. the even-odd/neg induction assembling the bridge.

## 4. Conclusion

- Actual: `smulEval` with genuine bivariate `φ, ω, ψ`; base values
  `n=0,1`; point bridge at `n=0,1`; `ω` evaluation laws already in S1410.
- Exact: group-law identities and universal polynomial identities for the
  full `zsmul_eq_smulEval`.
- No fake bridge/middle coordinate; EXIT=0.
