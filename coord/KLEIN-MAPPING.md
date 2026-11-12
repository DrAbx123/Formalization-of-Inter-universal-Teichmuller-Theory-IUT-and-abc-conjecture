# KLEIN-MAPPING — theta 特征 ↔ Klein form × eta 幂（Kubert–Lang）(A1097)

| field | value |
|---|---|
| Status | ANALYSIS (no Lean; no compile)；恒等式为 LITERATURE（Kubert–Lang, Modular Units, Grundlehren 244, Ch.1） |
| 结论 | 恒等式标准（权重检验 theta 1/2 = Klein 1 − eta 1/2 ⇒ m=−1）；形式化清单见 §2；我们的 u_j 需 (D1)-(D5) 才能对应 Klein 参数 (a,b)（GAP-MODPOINT）；恒等式 = A（LITERATURE），映射 = A 条件 |

## 1. Kubert–Lang 恒等式（模板与精确指数）

```
weight(theta[α,β]) = 1/2,  weight(Klein_{a,b}) = 1,  weight(eta) = 1/2
theta[α,β] = c(α,β) * Klein_{a,b} * eta^m  ⇒  1/2 = 1 + m/2  ⇒  m = -1
即  theta[α,β](z,tau) = c(α,β) * Klein_{a,b}(z,tau) / eta(tau)
```
- 精确常数 `c(α,β)`：按 Kubert–Lang Ch.1 的归一化抄录（含 `e^{-πi a b}` 相位）；
- 指数 `m = −1` 由权重决定；若采用其他 Klein 归一化可能差一个 eta 幂，以原文定义为准。

## 2. 形式化所需事实清单

1. 带特征 theta 定义：`theta[α,β](z,τ) = Σ_n exp(πi(n+α)²τ + 2πi(n+α)(z+β))`；
2. Dedekind eta：`η(τ) = e^{πiτ/12} ∏_{n≥1}(1−e^{2πinτ})`，收敛/非零；
3. Klein form 按 Kubert–Lang 定义（theta 商 × eta 幂）；
4. 变换律：theta/Klein 的平移与 `τ ↦ −1/τ` 因子；`η(τ+1)=e^{πi/12}η(τ)`、`η(−1/τ)=√(−iτ)η(τ)`；
5. q-展开比较（两边首项 + 变换律 ⇒ 恒等式）；
6. 相位常数 `c(α,β)` 显式值（对照原文）；
7. 特例核验：`(α,β)=(0,0)`、`z=0`；
8. Kronecker 极限公式给出 `|η(τ)|` 显式；
9. `|Klein_{a,b}(z)|` 由 1、8 得显式；
10. 乘积 `∏_j |theta(u_j)|^{j²}` 的显式表达；
11. Siegel units 整性（Kato/Robert）⇒ 有限位整性。

## 3. u_j 与 Klein 参数 (a,b) 的对应数据

```
(D1) E/F 椭圆曲线与复嵌入 σ : F → C；
(D2) 周期 τ_σ（E_σ(C) ≅ C/(Z+τ_σZ)）；
(D3) 水平 N（l-幂，与 ℓ-torsion 相关）；
(D4) N-torsion 基与坐标 (a_j,b_j) ∈ (1/N Z)²，u_j = a_j + b_j τ_σ；
(D5) theta 特征 (α_j,β_j) = (a_j,b_j)（或差已知平移/符号）。
```
**仓库现状**：`S2717QPilotLogVolume`/`S3016StepVQPilot`/`sourceQPilotSignedLog` 是标量，
没有 E(C) 点模型；S1487 有 Gaussian q-参数与 l/λ 数据，但没有周期 τ_σ 与 N-torsion 坐标。
⇒ 需新增 (D1)-(D5)（GAP-MODPOINT）。

## 4. 判定

| 子命题 | 类型 | 理由 |
|---|---|---|
| `theta[α,β] = c·Klein_{a,b}·η^{-1}` | **A（LITERATURE）** | Kubert–Lang 标准恒等式 |
| `∏ theta(u_j)^{j²}` 的 Klein 表示 | **A 条件** | (D1)-(D5) 齐备后逐项代入 |
| u_j 的曲线/模点数据 | **GAP-MODPOINT** | 当前只有标量，无曲线点 |
| arch 显式界 | **A 条件** | Kronecker/Siegel 公式（FEAS-KLEIN） |

## 5. Lean 签名草案

```lean
structure ThetaChar where
  N : Nat
  a : Real
  b : Real
  z : Real
  tau : Real
  thetaValue : Real
structure KleinValue where
  a : Real
  b : Real
  z : Real
  tau : Real
  value : Real
structure EtaValue where
  tau : Real
  value : Real
def KubertLangIdentity (T : ThetaChar) (K : KleinValue) (E : EtaValue) (c : Real) : Prop :=
  T.thetaValue = c * K.value / E.value
structure QPilotPointData where
  curveData : Prop
  tauSigma : Real
  level : Nat
  coords : Fin 1 → Real × Real
```

## 6. 结论

1. Kubert–Lang：`theta[α,β] = c(α,β)·Klein_{a,b}·η^{-1}`（权重检验 m=−1；常数需按原文抄录）；
2. 形式化清单：定义/变换律/q-展开/相位常数/Kronecker/Siegel（§2）；
3. u_j 需要 (D1)-(D5)（E/F、复嵌入、周期、水平、N-torsion 坐标）才能对应 (a,b)（GAP-MODPOINT）；
4. 恒等式 = A（LITERATURE）；映射 = A 条件；数据缺口 = GAP-MODPOINT；
5. 与 A1098 一致：当前 q-pilot 无模解释，需新增曲线/level 数据。