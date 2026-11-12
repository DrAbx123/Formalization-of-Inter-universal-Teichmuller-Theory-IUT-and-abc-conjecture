# GAP-ONLY-PLAN — 只攻我们的弱版 `M = V+gap−(sF−1)A ≥ 0` (A1107)

| field | value |
|---|---|
| Status | PLAN (no Lean, no compile) |
| 目标 | **只**证我们的 variant `M = V+gap−(sF−1)A ≥ 0`（⇔ `rhs ≥ −A`）；**绝不**使用/尝试 lana 的无 gap 强版 `SSIneq`（`V ≥ (sF−1)A`） |
| 关键恒等 | `gap = rhs + sF·A − V` ⇒ `M = A + rhs`（**V 与 gap 精确抵消**） |

## 1. 证明结构：gap 如何“吸收” V 的不足

定义（Gap:521-527）：
```
gap := rhs + sF*A - V,       rhs = -|log Θ|,  V = logVol(hull vcI)
M   := V + gap - (sF-1)*A
```
代入：
```
M = V + (rhs + sF*A - V) - (sF-1)*A = rhs + A
```
因此：
```
M ≥ 0  ⇔  A + rhs ≥ 0  ⇔  rhs ≥ -A      （即 Cor 3.12 / 我们的 variant）
```
- **V 在 M 中完全抵消**；V 的不足（`V < (sF−1)A`）由 `gap` 的定义**自动**补上，
  不是额外假设：gap 不是独立量，而是 `V` 与 `rhs` 的差的重编码；
- 因此证明目标只剩一条：`rhs ≥ −A`；`V` 只在中间式子里出现（作为恒等式的记账项）。

## 2. 禁止的强版形态（所有引理/假设都不得含）

```
✗ SSIneq:           V - (sF-1)*A >= 0        （lana 无 gap 强版）
✗ V >= (sF-1)*A                               （等价强版）
✗ gap >= 0 作为目标（gap≥0 ⇔ rhs + sF A - V ≥ 0；这是 lana 的另一不等式，不是我们的 M≥0）
✗ Cor312VariantHolds / Wall / Thm311 / lana 的 gap_nonneg 作为假设
```
允许的假设/结论（弱版，无强不等式）：
```
✓ N5Weak A rhs 0      （定义上 ⇔ -A ≤ rhs，正是我们的目标）
✓ QPilotThetaContainment（结构对象，⇒ -A ≤ -R = rhs）
✓ SignedQRegionData / signed 栈（qRegion ⊆ hullRegion ⇒ signedQ ≤ signedTheta）
✓ ThetaSectionData（degree ≤ 0，条件域）
✓ StepV box（rhs 的**上界**链；不单独给下界）
✓ per-place / parity 条件（A1078，纯代数归约）
✓ 单调性/haarLogVolume/area 工具
```
**检查结论**：上述允许项均**不含** `V ≥ (sF−1)A` 或 SSIneq 形态；
任何出现 `V ≥ (sF−1)A` 的推导即视为越界（须改写/剔除）。

## 3. 用已有 green 拼装时 gap 出现在哪一步

| 组件 | 在证明中的位置 | 与 gap 的关系 |
|---|---|---|
| `Mzk1N5WeakSkeletonActual.N5Weak A rhs 0` | 目标 ⇔ `−A ≤ rhs` | gap 不出现（rhs 抽象） |
| `Mzk1StructuralTargetActual.target_of_containment` | 结构对象 ⇒ `−A ≤ −R = rhs` | gap 不出现 |
| `Mzk1QRegionInclusionActual.variant_rankone_conditional` | `thetaRegion ⊆ qRegion ⇒ −A ≤ −R` | gap 不出现 |
| `Mzk1ThetaSectionActual.hcmp_of_theta_section` | `degree ≤ 0`（条件域） | gap 不出现 |
| StepV box（`Mzk1PaperStepVBoxActual`） | 给 **rhs ≤ P − sF·A**（上界） | 用于 lana 的 gap≥0 方向；**不是**我们下界 |
| per-place/parity（A1078） | `PerPlaceDeficit ⇒ 0 ≤ M_perPlace` | 把 gap 分配为 ind2 的记账形式 |
| `SYMBOLIC-INPUTS.md` | gap 的 per-i/v/c 展开 | 恒等（gap = (1/nC)ΣΣ gapHullAt） |

**gap 出现的唯一实质位置**：当我们把 `V` 与 `rhs` 分开记账时（per-place 分解、StepV box 代入），
但最终结论都化为 `M = A + rhs`，gap 不再是独立假设。

## 4. Concrete 验证（S1487 数值情景）

取 ℓ=5, nC=2, sF=2.5：(sF−1)=1.5。设（示意数值，非仓库硬编码）：
```
A    = 10     （高 qOrder 情景：qOrder 大 ⇒ A = Σ w qOrder log p/(2l) 大）
V    = 5      （V < (sF-1)A = 15，V 明显不足）
rhs  = -10    （Cor 3.12 等号情景：rhs = -A）
gap  = rhs + sF*A - V = -10 + 25 - 5 = 10
M    = V + gap - (sF-1)*A = 5 + 10 - 15 = 0     ✓（variant 成立）
```
- 展示：**V 不足以覆盖 (sF−1)A（5 < 15），但 gap=10 补足，M=0**；
- 若取低 qOrder 使 A 小（如 A=1）：V=5 ≥ (sF−1)A=1.5，V 本身已够（gap 仍非负但不必需）；
- 因此 **高 qOrder/大 A 情景**正是 gap 必需的情形；这也解释 lana 强版（去掉 gap）在高 qOrder 下不可证；
- 数值核对：`absNorm qPilotIdeal = 5²·2161²`，`A = [w_5 qOrder_5 log5 + w_2161 qOrder_2161 log2161]/(2ℓ)`；
  qOrder 的具体值需从 S1487 concrete 数据提取（GAP: S1487 qOrder extraction）。

Lean 形式（真证恒等）：
```lean
theorem M_eq_A_add_rhs {V gap A rhs sF : Real}
    (hgap : gap = rhs + sF*A - V) :
    V + gap - (sF-1)*A = A + rhs := by
  rw [hgap]; ring

theorem M_nonneg_iff {V gap A rhs sF : Real}
    (hgap : gap = rhs + sF*A - V) :
    0 ≤ V + gap - (sF-1)*A ↔ -A ≤ rhs := by
  rw [M_eq_A_add_rhs hgap]; constructor <;> intro h <;> linarith
```
（这两条应是下一批 Lean 的第一条：把 `M` 的定义与 `rhs ≥ −A` 精确绑定。）

## 5. 结论与下一步

1. `M = A + rhs` 是**恒等**（gap 定义为 rhs + sF A − V）；V 的不足被 gap 精确吸收，
   目标 ⇔ `rhs ≥ −A`（我们的弱版）；
2. 所有允许假设/引理均**不含** `V ≥ (sF−1)A` / SSIneq；强版被明确排除；
3. green 拼装中 gap 只在记账位置出现（per-place、StepV box 代入），最终都化为 `M = A + rhs`；
4. concrete 情景（ℓ=5, A=10, V=5, rhs=−10, gap=10, M=0）展示 gap 的必要性；
5. 下一步：先形式化 `M_eq_A_add_rhs`/`M_nonneg_iff`（纯代数），再把 N5Weak(0)/StructuralTarget/signed 栈
   接到 `rhs ≥ −A`；**不要**引入任何无 gap 强版假设。