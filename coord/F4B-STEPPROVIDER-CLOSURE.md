# A480: f4b → StepProvider 收口分析（shehdd）

## 收口链条（全部证据为已编译 tree/paper 资产）

1. **f4b（numMaxP/lex 严格下降）已 PROVED**：
   - LeanFormal/IUT 外 paper 层: tmp/sheaf/xif/paper/Mzk1NestedInductionActual.lean: `measure_stepSet_lt`, `maxDeg_stepSet_le`, `numMax_stepSet_lt`, `maxDegP_image_ofFinite`, `numMaxP_image_ofFinite`；
   - tmp/sheaf/xif/paper/Mzk1F0StepGeometryActual.lean: `f0StepTarget`, `f0StepTarget_maxDeg_le`, `f0StepTarget_measure_lt`, `f0StepTransportData`。
2. **f5（Target 沿 f0 回传）PROVED（条件于 CVCompositionLawF）**：
   - tmp/sheaf/xif/paper/Mzk1NestedInductionStepProviderActual.lean: `stepSetP`, `stepTransport_of_goal`（组合 f0Map_comp + aeval_comp；目标 S' (f0 beta) → S beta）。
3. **StepProviderFixedBetaChoiceInput（fixed-beta）剩余缺口 = 2 个显式 named 输入**：
   - `CVCompositionLawF`（临界值复合法则，F-层点形式）；
   - 归一化 f0 存在且 f0(beta) ∉ S'（解析回避层）。

## 新收口定理（本轮产物）

- tmp/sheaf/xif/paper/ShehddF4bStepProviderClosureActual.lean:
  - `f4b_stepProvider_closure_chain`：一次给出 f4b measure 严格下降 + f5 Target 回传（条件仅 CVCompositionLawF）；
  - `f0StepTransportData_closure_chain`：f0 step transport data 的 target/measure 字段全由已证定理给出。
  - 已入 dag/watchdog/extra-targets.txt。

## 结论与剩余

- f4b 不再是缺口（已证），fixedBetaChoice 从“两独立 named”收口为“CVCompositionLawF + analytic avoidance”两个明确输入；
- 若后续把 `CVCompositionLawF` 形式化（Mathlib 已有 derivative/aeval comp 工具，属可攻项），`StepProviderFixedBetaChoiceInput` 只剩解析回避层（另一 owner 的 f0 几何构造）。
- 不删历史；未碰 watchdog、未手动编译、未改 fragment。

## CVCompositionLawF 已证（A480 本轮新结果）

- tmp/sheaf/xif/paper/ShehddCVCompositionLawProvedActual.lean:
  - cvCompositionLawF_proved: 用形式导数链式法则 Polynomial.derivative_comp + mul_eq_zero + Polynomial.aeval_comp，对 Qbar 上任意多项式证明临界值复合法则（原 named input）；
  - stepTransport_of_goal_unconditional: stepTransport_of_goal 现在不再需要 CVCompositionLawF 假设。
- 因此 fixedBeta 收口后剩余 named 输入只剩: 归一化 f0 存在且 f0(beta) 不在 S'（解析回避层）。
- stepProvider 收敛仍需该几何回避层；CV 侧已闭合。
