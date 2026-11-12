# THREE-ROUTES-TEST — α/β/γ 路线试验设计、判定与当前状态

Date: 2026-11-12 (A876). Scope: ROUTES-FINAL-GAP §10 的三条研究性路线。**本文件只登记试验设计与状态，不把任何试验结果当作定理/证明。**

## 0. 结果文档

| route | 结果/设计文档 | 当前状态 |
|---|---|---|
| α 模性 + Shimura / Brandt | `coord/BRANDT-EXPERIMENT.md` | **NOT EXECUTED**；Lean 接口 green（`Mzk1BrandtExperimentInterfaceActual`），无数值数据 |
| β Fargues–Fontaine 局部容器 | 无独立结果文档；设计见 `ROUTES-FINAL-GAP §10 β` | **局部计算中**；尚无结果/结论 |
| γ Buium 算术 Kodaira–Spencer | `coord/BUIUM-EXPERIMENT.md` (A794/A795)、`coord/BUIUM-EXPERIMENT2.md` (A876) | **数值实验已做；γ 分支暂停/淘汰（见 §3）** |

## 1. α — 模性 + Shimura 曲线 / Brandt 试验

- **设计**: 按 ROUTES §12.3(a)，对素导子 `N < 10^5` 的曲线：算 p 处超奇异同源图/Brandt 矩阵 `B(p)` 在 `X_0(N)`-new 部分；取相关 Hecke 算子的本原整本征向量 `v`；检验配对恒等式 `||v||^2 = delta * e_p`；记录谱隙、delocalization (IPR)，看 `||v||^2/delta` 是否与图不变量相关。
- **输入**: 素导子曲线族（如 Cremona/LMFDB 数据）、p 处 Brandt 矩阵/超奇异同源图、`delta` 与 `e_p` 的独立计算；Lean 侧 `BrandtExperimentData` 字段（`conductor, matrix entries, eigenvector, normSq, delta, ramification, pairingIdentity, spectralGap, delocalization`）。
- **判定标准**: 若 `||v||^2 = delta*e_p` 被验证，且 `||v||^2/delta` 的小性/行为与图不变量（谱隙、IPR）有可计算相关，则 α 存活；若小性只能由 level lowering 解释、且与任何图不变量无关，则 α 被否决（`DeflationCriterion`）。
- **当前状态**: `BRANDT-EXPERIMENT.md` 明示 **NOT EXECUTED**；没有数值数据、没有 α 结论。Lean 只有接口，所有数值字段待填。
- **存活条件**: 数据中观察到非平凡的 graph-invariant 解释，且能给出不依赖 level lowering 的 norm 下界机制。
- **否决条件**: `||v||^2/delta` 的小性完全由 lowering 解释，或图不变量无相关；此时 α 的 Brandt 机制不成立。

## 2. β — Fargues–Fontaine 局部容器计算

- **设计**: 固定一个坏位，在 FF adic 曲线的半径参数 `ρ` 的允许区间内，计算 Θ 值区域之并的 log-volume；与需求 `(j²−1)·A` 对照；再检查各素数 `ρ_p` 能否独立选取。
- **输入**: FF adic 曲线/Teichmüller 元 `[q♭]` 的 Gauss 范数模型；`ρ` 允许区间与 `p`-adic 半径关系；固定坏位的局部数据、`j`、`A`、`q` 的归一化赋值。
- **判定标准**: 若 union log-volume 被 `(j²−1)A` 控制且需要整体约束（`ρ_p` 不能独立），则 β 有候选机制；若 `ρ_p` 可独立选取导致上界丢失，则 β 死。
- **当前状态**: **局部计算中**；无结果文档、无数值/Formula。不得把“进行中”当作支持证据。
- **存活条件**: 计算给出明确 union-volume 不等式，并且独立性检验为“不可独立”（或独立但整体预算仍闭合）。
- **否决条件**: `ρ_p` 独立可选使 union volume 超预算，或计算只能复述已知 6.5 节开关而没有新界。

## 3. γ — Buium 算术 Kodaira–Spencer 数值实验

- **设计**: 对 Szpiro 比高的曲线族算 p-导数不变量 `v_p(f¹_p(E))`（或 p-曲率深度 `T`），与 Szpiro 余量 `M=(1/6)log|Δ|−log N` 做相关分析；预登记判据要求 `|partial correlation| ≥ 0.5`、独立家族复现、`n ≥ 100`、规范 Teichmüller/Serre–Tate 提升。
- **输入**: Frey 曲线族（A+B=C）、`Δ`、`N=rad(ABC)`、p-曲率/算术 KS 不变量的可计算实现、独立家族数据。
- **判定标准**: 四个预登记条件全满足才保留候选；任一不满足则 γ 的“p-曲率深度 ↔ Szpiro 余量相关”分支暂停。
- **当前状态**: **已执行并暂停**。A794：`v_p(c4)` 廉价代理对所有奇坏素数结构性为 0，只有 `log16`，淘汰。A795：真 p-曲率 `T`（p=5..199，129/129 与 a_p 验证）std=5.00，但与 `M` 的 Pearson −0.035、偏相关 −0.036（n=37）；三个判据全不满足。BUIUM-EXPERIMENT2：Szpiro 侧可复现，但 Buium 不变量在仓库/vendor 无实现，无法计算相关；不伪造数据。
- **存活条件**: 实现规范提升 + 独立家族 + n≥100，且 |偏相关|≥0.5 复现；或找到新的非廉价 p-曲率不变量。
- **否决条件**: 廉价代理零方差；真 p-曲率与 M 无相关；无法实现规范提升/独立复现。当前全部指向否决/暂停。

## 4. 汇总

| route | 试验类型 | 当前状态 | 存活? | 否决/暂停理由 |
|---|---|---|---|---|
| α | Brandt 矩阵数值 | NOT EXECUTED（接口 green） | 未判定 | 无数据；不能宣称存活 |
| β | FF 局部计算 | 进行中 | 未判定 | 无结果；独立性检验未做 |
| γ | Buium 数值相关 | 已执行 | **NO（暂停）** | 廉价代理淘汰；真 p-曲率无相关；规范提升缺失 |

结论：目前三条路线 **没有一条产生可入证明链的结果**。γ 已有否定证据（暂停）；α/β 仍是 open 试验。任何后续更新应优先填 α 的 Brandt 表或 β 的局部 union-volume 计算，而不是宣称路线成功。
