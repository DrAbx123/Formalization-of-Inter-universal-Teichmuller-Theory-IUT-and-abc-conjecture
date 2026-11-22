# H-T F4/F5 实际构造计划（andrew, 2026-11-17 20:40）

## 0. 结论前提

route §8.3/§8.4 的 F4/F5 实际构造需要 tree 中**尚不存在的 scheme/divisor 几何层**；当前树只有：
- `Mzk1HT83F4PolyActual.RouteF4PolyData`（NO INHABITANT；字段含 `hE_le`/`hnorm` 两条高度假设）；
- `Mzk1HT84F4F5InterfaceActual.F5Statement`（NO INHABITANT）；
- `Mzk1G1F1HeightTransportActual.F1HeightTransportData`（Čech 框架，不含实际 O(1) 高度）；
- `Mzk1G1FermatCurveActual.fermatCurveScheme`（Y_n 作为 scheme，但**没有** homogeneous coordinate ring / O(1) line bundle / divisor-height API）。

因此 F4/F5 **不能**以“直接证明”方式落码；本文件给出 route 构造到 Lean 的精确分解、已有件与缺口。**不计闭合**。

## 1. F4（route L752-774）分解

### 1.1 构造对象
对每个固定边界 `E_i = φ_i^{-1}({0,1,∞})` 的每个几何点 `x ∈ E_i`：
1. 选过 `x` 但不含 `Y_n` 的直线 `L_x`（homogeneous linear form on ℙ²）；
2. 取 `x` 的有限 Galois orbit `O_x`，`P_{i,x} := ∏_{σ} L_{σ x}`（系数降到 ℚ，`Y_n` 不可约 ⇒ 不恒零）；
3. `P_i := ∏_{x/∼} P_{i,x}`（按 orbit 乘），`r_i := deg P_i`；
4. `div(P_i|_Y) = E_i + F_i`（`F_i ≥ 0` effective），固定 effective divisor height 有统一下界。

### 1.2 需要但缺失的 Lean 对象
- `Y_n` 的 homogeneous coordinate ring（`ℚ[x0,x1,x2]/(x0^n+x1^n−x2^n)`）与 `Proj` 模型；
- `O_Y(1)` 的 line bundle 与 Arakelov/divisor height `h_{O_Y(1)}`（不是抽象 F1 data）；
- divisor `div(P_i|_Y)`、effective divisor `F_i` 与高度 `h_{F_i}` 的非负下界；
- Galois orbit 作用于 scheme 点的 API（或等价的 prime/ideal orbit + trace 下降构造）；
- 除数高度 functoriality：`h_{div(P_i|_Y)}(y) ≤ r_i h_{O(1)}(y) + C_i`。

### 1.3 现有可复用件
- `Mzk1HT83F4PolyActual`：`RouteF4PolyData`、`RouteF4Statement`、`routeF4_of_polyData`（算术桥 DONE）；`kappa_nonneg`/`kappa_eq_mul_inv` DONE；
- `Mzk1G1F1HeightTransportActual`：Čech cover/transition/H0 frames（框架 DONE，但非实际 O(1) 高度）；
- `Mzk1G1FermatCurveActual`：Y_n scheme（可作底层）。

### 1.4 分阶段实现
- Stage A（可先做，纯代数）：定义 `F4PolyDataActual`（P_i : MvPolynomial (Fin 3) ℚ、`IsHomogeneous`、`natDegree`），证 `kappa_i = r_i/(n−3)` 与 `r_i hO1 = κ_i hOmega` 的代数恒等；此 stage 不声称 F4。
- Stage B（需 scheme/divisor 层）：实现 1.2 的 O(1)/divisor height API 与 Galois orbit 构造，证 `P_i|_Y` 非零与 `div = E_i+F_i`。
- Stage C：由 divisor functoriality 得 `hE_le`，填入 `RouteF4PolyData`，用 `routeF4_of_polyData` 得 F4。

## 2. F5（route L776-806）分解

### 2.1 构造
由 D1 施于 `φ_i(y)`（degree ≤ n²）+ F1（height transport）+ F2/F3（conductor/different）得：
`(1−η κ_i) h_ω(y) ≤ (1+η) D(L) + C`；取 `κ=max κ_i`、`η=δ/(2(1+(1+δ)κ))` 得统一 F6 常数。

### 2.2 需要但缺失
- D1 的实际 `LocalHeightCriterion`（现在只到 `D1AnalyticInput` 条件；`d1_of_analyticInput` DONE，但 `upper_estimate` 依赖 C4/D2 实际字母）；
- F1 的实际 height transport `h_{O(1)}(φ_i(y)) = ...`（抽象 F1 data 未实例化到实际 O(1)）；
- F2/F3 的实际 conductor/different cancellation（alan；当前 `F2`/`F3` interface NO INHABITANT）；
- `h_ω` 与 `h_{O(1)}` 的 κ 归一化（需 A4 实际线丛）。

### 2.3 现有可复用件
- `Mzk1G1F6EtaChoiceActual.routeF6_of_F1_to_F5_choice` DONE（η 选择算术，已消三假设）；
- `Mzk1G1F5F6ConsumeActual.f6_eta_choice_consumption` DONE（F5→F6 消费形状）；
- `Mzk1HT84F4F5InterfaceActual.f4_f5_combined`/`f5Statement_of_labelTl`（结构算术 DONE，输入 NO INHABITANT）。

### 2.4 分阶段实现
- Stage A（可先做）：把 F5 的 route 推导写成显式接口 `F5DerivationData`（D1 输出、F1 等式、F2/F3、κ 归一化），算术部分（`(1−ηκ)hω` 比较）用实数引理完成；不声称 F5。
- Stage B：等 F4 Stage B/C + alan F2/F3 + D1 实际 `LocalHeightCriterion`，实例化 `F5DerivationData`。

## 3. 与 P8 的关系
- P8 `perTriple` 的 F6 输入需要 F5 的实际数据；F5 未实际化前，P8 的 C6 保持条件（审计 §2 F5/F6 行）；
- F8/F9/transport 已 DONE，不受 F4/F5 影响；
- 本计划不计任何节点闭合；F4/F5 仍为 **NO INHABITANT**。

## 4. 建议
1. 先做 F4 Stage A（纯代数，小件，可 DONE）；
2. scheme/divisor O(1) height API 是大件，需 Lead 决定 owner（建议与 grace B3 scheme height / henry Y_n 协调）；
3. F5 Stage A 可并行（实数算术 + 显式接口），但终版依赖 F4/F2F3/D1。