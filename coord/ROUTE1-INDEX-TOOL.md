# ROUTE1-INDEX-TOOL — A1–A4/A8 工具盘点与结论（task-77）

日期：2026-11-13（快照约 04:20 Asia/Shanghai）。**只读审计 + 写工具文件；未自行编译**（统一编译约定：watchdog 负责）。

## 1. 产物

| 文件 | 说明 |
|---|---|
| `tmp/sheaf/xif/paper/Mzk1LatticeOrbitIndexActual.lean`（4,783B） | A-Index 工具 Lean 文件；已写入，**PENDING-WATCHDOG**（在 extra-targets，尚无 START/olean） |
| `coord/ROUTE1-INDEX-TOOL.md`（本文件） | 盘点、结论、A8 应用到 paperRootThetaImage 的判定 |

## 2. 已实现内容（Lean，file/line 以当前文件为准）

| 编号 | 声明 | 内容 | 状态 |
|---|---|---|---|
| A1 | `latticeStepQuotientEquiv` | Submodule 第二同构：`B/(B∩A) ≅ (B+A)/A`（Mathlib `LinearMap.quotientInfEquivSupQuotient` 的 handoff 形式） | 已写；**待 watchdog** |
| A2 | `latticeIndex`, `haar_measure_eq_index_mul_of_le` | 对紧开 `L ≤ K`：`μ K = #(K/L)·μ L`，复用 `CompactOpenAddSubgroup.measure_eq_index_mul_intersection`（实际 Haar） | 已写；**待 watchdog** |
| A3（单步） | `normalizedLogVolume`, `normalizedLogVolume_step` | `λ(K)−λ(L) = (1/d)·log #(K/L)`（实际 Haar index + log） | 已写；**待 watchdog** |
| A3（全链） | — | `λ(L_r)−λ(L_0)=(1/d)Σ log#C_i` 的有限链归纳 | **PENDING**（待单步编译通过后补） |
| A4 | — | `μ(L+L')·μ(L∩L')=μ(L)·μ(L')` | **PENDING**（应由 A2 两次 + A1 基数得到） |
| A8（集合核心） | `scalarAddEquiv`, `scalarLattice`, `orbit_scalar_comm` | 与公共标量交换的 `g`：`g(c·L)` 的标量格 = `c·g(L)` 的标量格 | 已写；**待 watchdog** |
| A8（Haar 比率） | — | `Σ O_E g(L_0(m)) = p^{a(m)} Σ O_E g(L_*)` 的**实际 Haar 比率不变性** | **PENDING**（需 A2 + 商指标同构；下一步） |

## 3. 复用与依赖

- 复用 `LeanFormal.IUT.Foundations.MeasureTheory.CompactOpenAddSubgroupIndex`：`intersectionInLeft`、`intersectionIndex`、`measure_eq_index_mul_intersection`、`relative_log_measure_eq_log_indices`；
- A2 是**实际 Haar** 的 index 公式（非集合等式）；A3/A4 都必须经它推导；
- A1 也可用 AddSubgroup 版本 `QuotientAddGroup.quotientKerEquivOfSurjective` 显式构造（已完成草图，暂未入文件，避免与 Submodule 版本重复）。

## 4. A8 应用到 paper 对象（lead 指定的一句话结论）

- **paperRootThetaImageNZ**：`= F(c_root)·O_hol`（`PaperNonzeroLabel` 排除 j=0，j²≥1，F 反单调；`S793PaperLeastLambdaOHullActual.lean:73-80`，`HANDOFF-OBJECT-TABLE §3.3`）。A8 ⇒ **相对 index/体积比与 a(m)=c_root=m/(2l) 无关，common-scalar 机制不产生随 m 线性增长的相对增益**；但绝对 normalized log-volume 仍含 a(m) 的线性项。
- **rootThetaHull（含 j=0）**：`rootThetaHull = closure(⋃_{j∈SignedLabel} rootThetaRegion j)`，j=0 项系数 0、等于 `F(0)·O_hol = R·O_hol`（q-无关固定分量，`HANDOFF-OBJECT-TABLE §3.2`）⇒ **该 hull 不是单一 `p^{a(m)}` 倍固定格，A8 的公共标量前提不成立；不能把 A8 直接用于 rootThetaHull，需把 j=0 的固定分量与非零标签分量分开处理**。

## 5. 判定与下一步

- 路线一工具核心（A1/A2/A3 单步/A8 集合）已就位；**A3 全链、A4、A8 Haar 比率仍缺**，在补齐前不能声称 route-1 工具完整；
- A8 结论对 paperRootThetaImageNZ 是**停止/无相对增益**判定（与 `HANDOFF §4.8` 一致）；rootThetaHull 需另立零标签处理；
- 待 watchdog 编译结果（START/DONE EXIT=0/FAIL + olean）后更新本表；若 FAIL，按 per-file log 修，不自行编译。

## 6. build 证据（当前）

- `Mzk1LatticeOrbitIndexActual.lean`：在 `dag/watchdog/extra-targets.txt`；截至本文件写入 **watchdog.log 无 START/DONE/FAIL**，`.lake/build/lib/lean/tmp/sheaf/xif/paper/Mzk1LatticeOrbitIndexActual.olean` **不存在** ⇒ **PENDING-WATCHDOG**（非 DONE）；
- 一旦 watchdog 出 DONE/FAIL，以 `dag/watchdog/watchdog.log` 行 + olean mtime 为准。

---

## 7. 编译与收尾记录（task-77 更新）

### 7.1 watchdog 首次 FAIL（20:21:19Z）与修复

首错（`dag/watchdog/logs/tmp_sheaf_xif_paper_Mzk1LatticeOrbitIndexActual.lean.log`）：

1. `:24:0 type of theorem latticeStepQuotientEquiv is not a proposition` → 返回 `≃ₗ`，改为 **`noncomputable def`**；
2. `:50:8 / :72:84` `measure_eq_index_mul_intersection/intersectionIndex_pos` 需要 `IsCompact K` → A2/A3 增加 `hKc : IsCompact (K:Set E)`，调用顺序改为 `K L hKc hKo hLo μ`；
3. `:76:35 rewrite 找不到模式`（`↑(latticeIndex L K) * μgapL` 的 toReal 强制转换）→ 先证 `harg : (μK).toReal = (latticeIndex : ℝ) * (μL).toReal`（`rw [hmeas, ENNReal.toReal_mul]; push_cast; ring`）再 `Real.log_mul`；
4. `:109:32 unsolved goals` A8 方向 → 用 `exact hg z` 代替 `simp [hg]`。

修复已保存（mtime 更新，watchdog 按 mtime 重试）；**未自行编译**。

### 7.2 仍未闭合（remaining gaps；若 lead 接受可标 completed 附此缺口）

- **A3 全链**：`λ(L_r)−λ(L_0)=(1/d)Σlog #C_i` 的有限链归纳（仅单步已写）；
- **A4**：`μ(L+L')·μ(L∩L')=μ(L)·μ(L')`；
- **A8 实际 Haar 比率**：`ΣO_E g(L_0(m))=p^{a(m)}ΣO_E g(L_*)` 的相对体积比与 m 无关（目前只有集合核心 `orbit_scalar_comm`）。
- 这些缺口未用 sorry/axiom 冒充；`coord/P1-MULTIFACTOR-BLOCK.md` 的 P1 前提中已列为 route1 未闭合项。

### 7.3 判定（A8 应用）

- `paperRootThetaImageNZ`（非零标签，`=F(c_root)·O_hol`, `c_root=m/(2l)`）：A8 给出**相对 index/体积比与 m 无关，common-scalar 机制不产生随 m 线性增长的相对增益**；绝对 log-volume 仍有 m 线性项。
- `rootThetaHull`（含 j=0）：j=0 贡献 `F(0)·O_hol=R·O_hol` 的 q-无关固定分量，hull 不是单一 `p^{a(m)}` 倍格 ⇒ **A8 前提不成立，不能直接套用；需拆出零标签固定分量**（HANDOFF-OBJECT-TABLE §3.2–3.3）。


---

## 8. 联动更新（23:45Z）

- A 线工具：`Mzk1DiagEquivProvedActual`（e'/map）、`Mzk1DiagQuotCardActual`（商/cardinal）、`Mzk1DiagVolumeProvedActual`（体积比）均 green；
- SNF 工具：`Mzk1SNFToolActual`/`Mzk1BasisDetUnitActual`/`Mzk1SNFDiagActual`/`Mzk1SNFDiagEquivActual`/`Mzk1GLActActual` green；
- `coord/XG-DIAGONAL-SOURCE-GAP.md §8–10` 已更新；剩余 GAP：一般 X_G GL_d(Z_p)-等价比（组合 SNF span + GL 保格 + det unit）、Ind1 桥反向。