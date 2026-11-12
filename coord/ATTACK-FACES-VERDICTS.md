# ATTACK-FACES-VERDICTS — 四条攻击面的不可行/可行判定

Date: 2026-11-12 (A899). **所有 lana 路径相对根 `Iut/` 树（`D:/lean/Iut/...`）。**

## 0. 用户定义（判定前提）

**换概念 / 换说法 = 不可行。** 只有真正证出一条新的数学命题（且有独立判据/定理名）才算可行；把目标重写成等价形式、给它换名字、或把缺口包装成新的 Prop/结构，都不算。

## 1. 判定总表

| face | 主张 | 判据（定理名/来源） | 判定 |
|---|---|---|---|
| **face1** | 等价改写 `qThetaPilotLogVolumeComparison` 即可 | `S3137QThetaPilotLogVolumeReadingsActual.qThetaPilotLogVolumeComparison_iff`（green；`Iff.rfl` 型展开） | **不可行**：只是定义展开/换说法，无新数学 |
| **face2** | 需要一条“新关系”把 q 侧和 Θ 侧连起来 | `Mzk1E7ReductionActual.e7_equiv_chain`（green；逻辑合取/拆分，`jointPackage` 仍是 Prop） | **不可行（作为当前路线）**：没有独立关系定理；把关系当假设=换说法/换概念 |
| **face3** | 走 q-power 链（q-scaling 幂/chainModel） | `Iut.ThetaLink.not_logShellCompat_qScale_zpow`（`ThetaLink/Wall.lean:145`）；`not_logShellCompat_chainModel`（`:294`）；`LinkedChain.kum_ne_chainModel`（`:299`） | **不可行（lana 已证不兼容）** |
| **face4** | 现有 wall 接口足够 | `Iut.Wall.Checks.exists_wall_iff`（`:173`）、`exists_isTrivial_iff`（`:162`）；`Iut/Wall/README.md:130` 明说 (T1)-(T3) too weak；`Iut.WallEquiv.NonDerivable.nonDerivability` | **不可行（lana 已证接口太弱）** |

## 2. face1 — 等价改写

- **主张**: 把 `qThetaPilotLogVolumeComparison`（`qPilotLogVolumeReading ≤ thetaPilotHullLogVolumeReal`）改写成另一种等价形式，从而“完成”链二。
- **判据**: `tmp/sheaf/xif/paper/S3137QThetaPilotLogVolumeReadingsActual.lean` 中 `qThetaPilotLogVolumeComparison_iff` 只是 `Iff.rfl`（定义展开）；green olean 存在。
- **结论**: **不可行**。按用户定义，等价改写/换说法不是证明；`iff` 只把同一命题换名，不能推出 `(s−1)A ≤ V`。

## 3. face2 — 需新关系

- **主张**: 需要一条新的关系（例如把 q-pilot 区域与 Θ 容器/体积连接起来）才能推进。
- **判据**: `tmp/sheaf/xif/paper/Mzk1E7ReductionActual.lean` 的 `e7_equiv_chain` green：`E7GapStatement ↔ E7Statement ∧ jointPackage`，只是逻辑拆合；`jointPackage` 的四个分量仍是 Prop fields，**没有一条独立关系定理**。`Mzk1RouteCInternalActual.FreyLogDictionary` 也只是定义/假设。
- **结论**: **不可行（作为当前路线）**。若把“新关系”作为 assumption 引入，就是换概念/换假设；若真能独立证明一条新关系，那是一个新定理，不属于 face2 的“换说法”操作。

## 4. face3 — q-power 链不兼容（lana 已证）

- **主张**: 用 q-scaling 幂（`qScale D ^ m`）/ drifting chainModel 的 q-power 链来连接各 theater/容器。
- **判据**（lana 源级；本地 olean 未产）:
  1. `Iut.ThetaLink.not_logShellCompat_qScale_zpow` — 非零 `m` 的 `qScale^m` 不满足 `LogShellCompat`（`Iut/ThetaLink/Wall.lean:145`）；
  2. `Iut.ThetaLink.not_logShellCompat_chainModel` — `k ≠ 0` 时 `Wall.chainModel D k` 的 Kummer 识别不保 log-shell（`:294`）；
  3. `Iut.ThetaLink.LinkedChain.kum_ne_chainModel` — 任何 `LinkedChain` 的 kum 都不等于 drifting `chainModel`（`:299`）。
- **结论**: **不可行**。q-power 链把 value-group（q-power）数据搬进 unit portion，破坏 log-shell compatibility；lana 已证该链与 log-shell 兼容性不相容，不能作为连接机制。

## 5. face4 — 接口太弱（lana 已证）

- **主张**: 现有 wall 接口（T1）–（T3）/`Wall D A` 足以承载证明。
- **判据**（lana 源级；本地 olean 未产）:
  1. `Iut.Wall.Checks.exists_isTrivial_iff`（`:162`）与 `exists_wall_iff`（`:173`）：存在 `A` 使 `Wall D A` **iff** variant；
  2. `Iut/Wall/README.md:130` 明说：(T1)–(T3) 作为算法存在量词接口 too weak，wall 只是 variant 的重述；
  3. `Iut.WallEquiv.NonDerivable.nonDerivability` 进一步证明 Step (xi) 不能从 Thm 3.11 的形式内容推出。
- **结论**: **不可行**。接口太弱导致 `∃ A, Wall D A` 与 variant 等价，不能提供独立上界；把它当证明就是循环/换说法。

## 6. 总结

- **face1 不可行**（等价改写=换说法）；**face2 不可行（当前路线；新关系若独立证出则是新定理）**；**face3 不可行（lana 证 q-power 链与 log-shell 不兼容）**；**face4 不可行（lana 证接口太弱/循环）**。
- 四条面当前都不能把链二从 `req ≤ U` 推进到 `(s−1)A ≤ VolShell P`。真正缺的仍是独立定理：`qPilotRegion ⊆ P ⇒ (s−1)A ≤ VolShell P`（平均版）；它必须作为新数学内容证明，不能由这四条面包装出来。
- 证据状态：face1/face2 的本地 Lean 文件 green；face3/face4 为 lana 源级证明，相关 `Iut/ThetaLink/Wall.lean`、`Iut/Wall/Checks.lean` 的本地 oleans 未产，引用时须注明“根 Iut/ 源级、olean 未产”。
