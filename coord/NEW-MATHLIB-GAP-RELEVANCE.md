# A506: Mathlib v4.33.1 新增 vs named gaps（hcomp/theta-hull/PNT）相关性（只读）

来源: `tmp/external/flt-lean/lake-manifest.json`（mathlib rev `db584cd6d46c92f209a44c0f1c829460d327499d`）、GitHub API（commit/compare/path commits）、本地 `.lake/packages/mathlib`（v4.32.2, HEAD `905b95818eb32af7874a58b427f50c1711a5e96c`）。只读；未改任何文件/队列/watchdog。

## 0. 先记两个事实（影响结论强度）

1. **本地 v4.33.1 checkout 不存在**：Lead 给的路径 `tmp/external/flt-lean/.lake/packages/mathlib` 在本仓不存在（`flt-lean/.lake` 整个缺失；全仓 `lean-toolchain` 扫描未发现 v4.33.* 的 mathlib；最近的是 iut4-sec1 v4.32.0、Takkun v4.31.0、根 v4.32.2）。因此**无法本地编译扫描**。
2. flt-lean 的 `lake-manifest.json` pin 的 mathlib rev 是 `db584cd6...`；GitHub API 显示它是 **“chore: bump toolchain to v4.33.0 (#42604)”，2026-08-10**。我们 HEAD `905b958` 是 **v4.32.2 bump，2026-07-28**。所以目标实际是 **v4.33.0 toolchain（Lead 写作 v4.33.1）**，两个 tag 相隔约 13 天；期间改动量本身不大。
3. 网络：GitHub API 前几次可访问（commit、path commits），随后 raw/compare 被 host 解析策略阻止（非公开 IP），因此**无法取全量 diff**；下表是已取到的 path/commit 级证据，不是全量文件清单。

## 1. 已取到的窗口内改动证据（2026-07-28 → 2026-08-11，按 path）

| Mathlib path | 窗口内 commits | 内容 | 与 named gap 关系 |
|---|---|---|---|
| `Mathlib/NumberTheory/PrimeCounting.lean` | 0 | — | **PNT 无新增** |
| `Mathlib/NumberTheory/Height` | 1 | `641fbd329d feat(Logic/Function/Defs): add Function.diag (#41082)` | 与高度比较无关（generic util） |
| `Mathlib/NumberTheory/Padics` | 1 | `f6dc05e369 chore(Topology/UniformSpace): rename complete_univ → isComplete_univ (#42163)` | 仅 rename，无 p 进 log/体积新引理 |
| `Mathlib/MeasureTheory/Measure/Haar` | 0 | — | **Haar/log-volume 无新增** |
| `Mathlib/Analysis/SpecialFunctions/Log` | 0 | — | **log 分析无新增** |
| `Mathlib/NumberTheory/NumberField` | 6：`5d2a6a3227` remove IsDedekindDomainDvr (#42367)；`f51bdaa421` wikidata (#41139)；`62f22e6344` **feat DirichletDensity (#41765)**；`e900b02601` deprecate apply_eq_iff_eq_symm_apply (#42094)；`21da9fc403` **adel e ring notation (#40535)**；`8ae3f0490e` **RelNorm 用 Module.finrank (#42175)** | 新增 `NumberField.DirichletDensity` 模块；adeles 记法；RelNorm 实现变更；其余文档/清理 | 只对 “PNT/素数分布/adelic 记账” 有间接意义；对 hcomp 的 height/volume 不等式、theta-hull 均**无直接新引理** |

> 说明：path 过滤只覆盖上述目录的 commit；新文件若落在别处（如新的 `Analysis/...` 模块）不在表中。compare JSON 被 100KB 截断，未见 files 数组；因此上表是**“已核对的直接路径无新增”**，不能声称全仓无其他改动。

## 2. named gaps 对照

### 2.1 hcomp 两条 IUT IV 比较（`Cor312ToABCBridgeInterface.Cor312EpsilonArithmeticComparison`：height ≤ (1+ε)·normalizedRegionVolume；regionVolume ≤ (1+ε)·weight + hullVolume + D）

- 窗口内 **Height 无相关新引理**；**Haar/Log 无新增**；Padics 只 rename；NumberField 的 DirichletDensity/adeles notation/RelNorm 均不提供 height-to-volume 或 volume-to-weight 的比较定理。
- 结论：**v4.33.0 没有可 cherry-pick 来关闭 hcomp 的 Mathlib 引理**。hcomp 仍是 named gap；只能靠我们自己的 literal IQ carrier/Haar/hull/det（O7–O9）+ paper-level 构造，或外部项目（Takkun Real* 等）作为对象/待审计数据（A500 规则：结论不作证明）。
- 可关注但非 gap-closing：`RelNorm` 用 `Module.finrank` (#42175) 可能影响我们 different/norm 记账的写法（适配风险而非新内容）；adelic notation (#40535) 仅是记号。

### 2.2 theta-hull（Θ-pilot hull log-volume / procession normalization）

- **Haar path 0 commits、Log path 0 commits、Padics 仅 rename**；`Measure.addHaar` 归一化问题（A498）没有新解（没有新的 canonical Haar/log-volume 归一化引理）。
- 结论：**无新增可直接用于 theta-hull 的引理**；继续用自有 `S3137/AbsTopIII09/C3 Haar log-volume` + literal IQ/hull 资产，以及 Takkun `RealFrobenioid/RealHodgeTheater`（对象层，待审计）。
- 如果后续要 cherry-pick，优先候选是 p 进 exp/log/Haar 的具体改进，但窗口内未见提交；需要重新拉取完整 v4.33.0 diff 才能确认。

### 2.3 PNT（Cor 2.2 素数选择 / [ExpEst] Cor 5.2 (C1)）

- `PrimeCounting.lean` 窗口内 **0 commits**；没有新的 PNT/Chebyshev/素数计数引理进入。
- 我们的 PNT 依赖仍在 Takkun `Diophantine/PrimeCountingBound`/`PrimeSelection`（外部，需审计）或自有/脚本；**v4.33 不解决**。
- 唯一新模块 `NumberField.DirichletDensity` (#41765) 是 Dirichlet 密度（算术级数/密度），不是 PNT 本身；也不直接给 Chebyshev bound。

## 3. 候选 cherry-pick 清单（低优先级，且需适配 v4.32.2）

| 候选 | 来源 commit | 可能用途 | 判定 |
|---|---|---|---|
| `Mathlib.NumberTheory.NumberField.DirichletDensity` | 62f22e6344 (#41765) | PNT/素数分布辅助（非 PNT 本体） | 低；若 Cor 2.2 选素数需要密度工具再取，需 API 适配 |
| adeles ring notation | 21da9fc403 (#40535) | O3/hcomp 的 adelic 记账/notation | 低；仅 notation，无定理 |
| `Module.finrank` in RelNorm | 8ae3f0490e (#42175) | different/norm 记账写法 | 低；适配风险，非新结论 |
| `Function.diag` | 641fbd329d (#41082) | generic utility | 无（与 gap 无关） |

**不建议**整体升级 v4.33.1（需重编 ~10k oleans，且上述证据显示 named gaps 无直接受益）。要 cherry-pick 时，必须先把 v4.33.0 mathlib 实际 checkout 到本地（当前 flt-lean 没有 `.lake/packages`），抽取目标 lemma 源码，改写到 v4.32.2 API（重点检查 `apply_eq_iff_eq_symm_apply` 弃用、`IsDedekindDomainDvr` 移除、`complete_univ` rename 等 API 漂移），再放入 `tmp/newmathlib/`。

## 4. 建议

1. **不升级、不 cherry-pick**：窗口内 PNT/theta-hull/hcomp 均无直接新引理；升级成本远大于收益。
2. **纠正路径/版本**：Lead 所述 `tmp/external/flt-lean/.lake/packages/mathlib` 不存在；flt-lean manifest 的 target 是 **v4.33.0**（commit db584cd6）不是 v4.33.1。请确认是否有另一份本地 checkout；若有，给出实际路径后我可在只读模式做文件级 diff/lemma 扫描。
3. **hcomp/theta-hull 路线不变**：hcomp 仍为 named gap；theta-hull 用自有 C3/Haar + literal IQ/hull；PNT 继续用 Takkun/自有（外部结论按 A500 只作数据）。
4. 若一定要尝鲜：先拉 v4.33.0 完整 diff，按上面 §3 候选逐个评估，避免整体升级。

## 5. 验证状态（诚实标注）

- 本地 v4.33.x checkout：**不存在**，未编译/未扫描；
- GitHub API：commit 元数据 + 6 条 path 查询成功；compare JSON truncated、raw fetch 被 host 策略阻断；
- 因此本文件的结论是 “已核对的 path 在窗口内无新增/无直接相关”，**不是** 对 v4.33.0 全量新增的穷尽证明；需完整 diff 才能下最终结论。

只读；未改任何文件/队列/watchdog。
