# Mzk1G1R3Psi2TwoGeneralActual — 设计稿（DRAFT，未入队）

日期：2026-11-18；owner：henry；依据：Lead 01:xx（Legendre 最小实例先行）与 grace 双数值验证。

## 目标（一般 Weierstrass 曲线，`d = 2y + a₁x + a₃`）
```lean
theorem psi2AtTwo_mul_cube_general {F} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) {x y : F}
    (hEq : W.polynomial.evalEval x y = 0)
    (hd : 2 * y + W.a₁ * x + W.a₃ ≠ 0) :
    psi2AtTwo W x y * (2 * y + W.a₁ * x + W.a₃) ^ 3 = (W.preΨ 4).eval x
```
等价形式（`M := d²·psi2AtTwo`）：`M * d = (W.preΨ 4).eval x`，在曲线方程模下成立。

## 证明计划
1. `psi2AtTwo_eq`（DONE）：`psi2AtTwo = -2ℓ(addX - x) - 2y - a₁addX - a₃`；
2. `two_nsmul_slope_eq`（DONE）：`ℓ = N/d`，`N = 3x²+2a₂x+a₄-a₁y`；
3. `addX = A/d²`，`A = N² + a₁Nd - (a₂+2x)d²`；
4. 乘 `d³` 得 `d³·psi2AtTwo = M3 := -2N(A-xd²) - (2y+a₃)d³ - a₁Ad`；
5. `preΨ_four`/`preΨ₄`/`b₂..b₈` 展开 RHS；
6. 用曲线方程 `y² + a₁xy + a₃y = x³+a₂x²+a₄x+a₆` 归约 M3（y 次数≤3 → 用 `linear_combination hEq * y^k` 消去 y² 项）；
7. `ring` 比较系数得恒等式；
8. 零等价：`psi2AtTwo = 0 ↔ preΨ₄ = 0`（`d³ ≠ 0`），再配 `Ψ4 = C preΨ₄·ψ₂` 得 `↔ ψ₄(P) = 0`。

## 触发条件
- 仅当 `Mzk1G1R3LegendrePsi2TwoActual.psi2AtTwo_mul_cube` **DONE** 且方法验证有效后才写此文件并入队；
- 若 Legendre 版失败：先修 Legendre（首个 error 是 y 奇次幂项或 `field_simp` 余式），此稿暂缓。

## 给 grace 的接口
- 她已有 `Mzk1G1R3FourNsmulActual.{four_nsmul_eq_zero_iff_evalDivisionPolynomialAtPoint_two_two_nsmul, Ψ4 = C preΨ₄·ψ₂}`；
- 一般 W 版绿 ⇒ `four_nsmul_some_eq_zero_iff_evalDivisionPolynomial_four` 直接合并。
