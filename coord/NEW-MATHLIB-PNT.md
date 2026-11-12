# NEW-MATHLIB PNT / Chebyshev scan (A506)

作者: stepxi. 只读扫描；不升级主构建。

## 1. 扫描目标与结果

- 指示路径: `tmp/external/flt-lean/.lake/packages/mathlib` (声称 v4.33.1)。
- 实际: `tmp/external/flt-lean` 存在，`lean-toolchain` = `leanprover/lean4:v4.33.1`，但 `.lake` 目录不存在，`Test-Path tmp/external/flt-lean/.lake` = false；没有本地 v4.33.1 mathlib 源码/olean。
- 仓库内实际可用的 mathlib 源码版本: 主 `.lake/packages/mathlib` v4.32.2；`tmp/external/iut4-sec1/.lake/packages/mathlib` v4.32.0；`tmp/external/Takkun-IUT_LEAN/.lake/packages/mathlib` v4.31.0。均不是 v4.33.1。
- 网络 `raw.githubusercontent.com` 当前不可达（web_fetch fetch failed），因此无法从 flt-lean manifest 的 rev 拉取 v4.33.1 源做在线 diff。
- 结论: 本次**无法本地扫描 v4.33.1 新增 PNT/Chebyshev/prime-counting 引理**；只能对照现有 4.32.2 资产和 Takkun/Section2。

## 2. 现有 Takkun 的 PNT/Chebyshev 资产

`tmp/sheaf/takkun/IutLean/Diophantine/PrimeCountingBound.lean`:

- `theta_le (n : Nat) : sum_{p in range(n+1), p.Prime} log p <= n * Real.log 4`，由 Mathlib `primorial_le_four_pow` 证明。
- `primeCounting_le_chebyshev (n : Nat) (hn : 2 <= n) :
    (Nat.primeCounting n : Real) <= (Nat.sqrt n : Real) + 1 + 4 * n / Real.log n`。
  这是 Chebyshev 弱常数版，**不是** paper Prop 1.6 的 `4η/(3 log η)`。
- 文件头 honest 注记: `4/3` 是 PNT 强度，当前 Mathlib 核未收录 PNT；弱常数版只适合看结构、常数劣化。

`tmp/sheaf/takkun/IutLean/Diophantine/Thm110.lean`:

- `cTheta_ge_neg_one (P : PilotVolumeData) (CTheta : Real)
    (hq_pos : 0 < -P.negLogQ) (hbound : P.negLogTheta <= CTheta * (-P.negLogQ)) : -1 <= CTheta`;
- `thm110_elementary_deduction`: 从 `(1/6)(1-12/l^2)logq <= (1+12d/l)D+10(e*l+eta)` 推
  `(1/6)logq <= (1+20d/l)D+20(e*l+eta)`，纯实数计算，不使用 PNT。

Takkun 未在 Diophantine 中使用 v4.33 新 PNT 引理；其 PNT 部分只有上述 Chebyshev 弱上界。

## 3. 我们 Section2 的 PNT/Chebyshev 资产（v4.32.2 已可编）

`LeanFormal/IUT/IUTIV/Estimates/Section2.lean`:

- `iutIVProp16_primeCounting_le_four_thirds_eventually :
    exists eta0 : Real, 0 < eta0 /\ forall eta : Real, eta0 <= eta ->
      (Nat.primeCounting floor(eta) : Real) <= 4 * eta / (3 * Real.log eta)`。
  证明用 Mathlib `Chebyshev.integral_theta_div_log_sq_isLittleO` + `primeCounting_eq_theta_div_log_add_integral` + `theta_le_thirteen_tenths_mul_add`；这已经是 4/3 常数。
- `iutIVProp16_index_le_four_thirds_nthPrime`: 第 n 个素数的 `n+1 <= 4 p_n/(3 log p_n)` eventually。
- `iutIVProp21ii_theta_two_sided_eventually`: `(2/3)x <= theta x <= (4/3)x` eventually。
- `iutIVProp21i_log_le_self` 等初等估计。

对照: Section2 的 `4/3` 比 Takkun 的 `π(n) <= sqrt n + 1 + 4n/log n` 强（后者随 sqrt 项增长，不能给出 4/3 常数）。Takkun 的用途是 Chebyshev-only 结构 / Thm110 初等段；我们 Section2 已足以支撑 ExpEst PNT Class B（见 `Mzk1ExpEst02RealizedActual`: `expEstPNTUpper_realized`, `expEstPrimeReciprocalSum_realized`, `expEstChebyshevTheta_realized`）。

## 4. v4.33.1 候选新引理清单（待源可用后执行）

若拿到 v4.33.1 mathlib 源码，先 diff 这些文件（与 PNT/Chebyshev/prime counting 最相关）:

1. `Mathlib/NumberTheory/Chebyshev.lean`
2. `Mathlib/NumberTheory/PrimeCounting.lean`
3. `Mathlib/NumberTheory/AbelSummation.lean`
4. `Mathlib/NumberTheory/SumPrimeReciprocals.lean`
5. `Mathlib/NumberTheory/PrimesCongruentOne.lean`（若涉及显式估计）
6. `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` / `Pow/Real.lean` 的新 explicit bounds
7. 新目录/文件: `Mathlib/NumberTheory/PNT/`、`Mathlib/NumberTheory/PrimeNumberTheorem*`（若 v4.33.1 新增）

扫描命令（源就位后）:

    git -C tmp/external/flt-lean/.lake/packages/mathlib rev-parse HEAD
    diff -u .lake/packages/mathlib/Mathlib/NumberTheory/Chebyshev.lean \
      tmp/external/flt-lean/.lake/packages/mathlib/Mathlib/NumberTheory/Chebyshev.lean
    rg -n 'primeCounting|Chebyshev.theta|theta_le|PNT|PrimeNumber|Rosser|Schoenfeld' \
      tmp/external/flt-lean/.lake/packages/mathlib/Mathlib/NumberTheory

只 cherry-pick 到 `tmp/newmathlib/`，以 v4.32.2 能编译的形式适配；不整体升级主构建。

## 5. 当前结论

- 本地无 v4.33.1 源码，不能声称找到任何新 PNT 引理；本次没有 cherry-pick。
- Takkun 的 Chebyshev 弱版不能替代我们 Section2 的 4/3 PNT 估计；Section2 已够 ExpEst02 Class B。
- 需要 v4.33.1 时，先补 `tmp/external/flt-lean/.lake/packages/mathlib` 或提供源/缓存，再按 §4 diff。

