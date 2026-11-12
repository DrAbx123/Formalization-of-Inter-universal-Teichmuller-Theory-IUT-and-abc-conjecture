# NUMBER-THEORY-FOUNDATIONS-A505 — 数论/高度侧可直接 import 的外部基础（不手写）

依据 A505 联合地基策略：Mathlib v4.32.2 + `tmp/local-cft-port` + 已端口化外部项目（`tmp/external/ported/`）+ Takkun（`tmp/sheaf/takkun`）+ 自有 `LeanFormal`。以下只列**可直接 import/复用的 file:decl**（不复制证明、不手写基础）；结论层/REQUEST 不采纳。

## 1) different / 微分 / 正则微分（Gap 1 的算术线丛-高度侧）

| 端口化文件 | 可复用 decl | 用途 |
|---|---|---|
| `tmp/external/ported/flt_core/Definitions/Def_AlgebraicCurve_RegularDifferentials.lean` | `regularDifferentials`（Submodule K Ω[F⁄K]）、`mem_regularDifferentials_iff`、`exists_ord_eq_one_and_dCoord_eq` | 正则微分空间与局部 ord/dCoord 存在性，为 IUT IV 线丛 log-volume 与高度的局部比较提供真实微分对象 |
| `tmp/external/ported/flt_core/Theorems/Thm_AlgebraicCurve_exists_linearEquiv_regularDifferentials_omegaSpace_zero.lean` | `hasSeparableResidue_of_perfectField`、`nonempty_place_of_constantsAreBase`、`canonicalDivisorOf_nonneg_of_mem_regularDifferentials`、`mem_regularDifferentials_of_canonicalDivisorOf_nonneg`、`kaehlerResidueTerm_*`、`kaehlerToWeil_apply` | 典范除子/Weil 微分/留数项与 adele 空间接口；Gap 1 中 height ↔ 线丛比较的代数-微分基础 |
| `tmp/external/ported/flt_core/Theorems/Thm_AlgebraicCurve_weilDifferentialRankOne_of_isCurveOver.lean`、`..._of_stichtenothGenusExists.lean` | `weilDifferentialRankOne`（同名定理；rank one 性质） | 线丛次数/微分 rank 的既有证明；可支撑 Gap 1 的 exponent/degree 记账（不手写） |

备注：`tmp/external/ported/flt_core` 与 `flt` 的同名 Definitions 重复（脚本移植冗余），import 时选 `flt_core` 一份即可。

## 2) 曲线/除子/高度基础设施

| 端口化文件 | 可复用 decl | 用途 |
|---|---|---|
| `tmp/external/ported/flt_core/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean` | `heightOneSpectrum`、`heightOneSpectrum_asIdeal`、`adicValuation` | 曲线的 height-one 位点与 adic valuation；高度侧局部化对象 |
| `tmp/external/ported/flt_core/Definitions/Def_AlgebraicCurve_RatFuncPlaces.lean` | `heightOneSpectrumOfIrreducible`、`heightOneSpectrumOfIrreducible_asIdeal` | 有理函数域位点构造（素多项式）；Gap 1 的高度位置参数化 |
| `tmp/external/ported/flt_core/Definitions/Def_AlgebraicCurve_PlaceCompletion.lean` | `adicCompletion` | 位点完备化；与 q-pilot 的 p-adic 值一致 |
| `tmp/external/ported/flt_core/Definitions/Def_ModularCurve_CanonicalDivisor.lean` | `differentialCoeff`、`ordDifferential`、`differentialCoeff_smul_dCoord`、`differentialCoeff_unique`、`ord_differentialCoeff_nonneg_of_mem_regularDifferentials` | 典范除子/微分局部系数；Gap 1/2 的 different 指数记账 |

## 3) PNT / Chebyshev 常数（Gap 2 显式常数）

| 文件 | 可复用 decl | 用途 |
|---|---|---|
| `tmp/sheaf/takkun/IutLean/Diophantine/PrimeCountingBound.lean` | `theta_le`（Chebyshev θ 上界）、`primeCounting_le_chebyshev`（`π(n) ≤ √n+1+4n/log n`） | 端口化外部项目中 PNT 命中为 0（grep 结果仅曲线例子 `chebyshevTriple`，非素数计数）；显式 PNT/Chebyshev 只能从 Takkun Diophantine 复用 |
| `tmp/sheaf/takkun/IutLean/Diophantine/LogVolume.lean` | `log_two_le_one`、`one_le_log_three`、`log_three_le_log_pi`、`log_pi_le_log_five`、`log_five_le_two`、`card_GL2` | Gap 2 的显式常数估值 |

## 4) 高度函数本身

- 高度不用外部再找：现有 `LeanFormal/IUT/ABCBridge`（`Height.logHeight₁`、`abcRationalPoint_logHeight₁`、`arithmeticWeight`/`IsABCTriple` 等在 `Cor312ToABCBridgeInterface.lean` 依赖链中）已是真实实现；A503 的 `HeightRegionObject`/`RegionWeightObject` 正是建在其上。
- Mathlib v4.32.2 提供 p-adic 范数（`Padic.norm_p`，已用于 O1 `qPilotValue_norm`）、`primorial_le_four_pow`（Takkun `theta_le` 的底层）等基础，无需自写。

## 5) 与 Takkun Diophantine 常数复用路径（确认）

1. Takkun 算术层可复用：`thm110_elementary_deduction`、`cor22_epsilon_form`、`cor22_uniform`（显式常数不等式）+ 上表 PNT/LogVolume 常数；
2. 不可直接复用：`PilotVolumeData`/`ArithmeticData`/`AdjudicationTest`/`hsupply` 是 Takkun 自有对象/假设，**不是**我们 hcomp Gap 1/2 的证明；复用前须完成对象语义桥（字段 → 我们 `logVolume`/`height`）；
3. 常数进入我们 `Cor312EpsilonArithmeticComparison` 的路径：Takkun ℝ 不等式 → A502 `ENNReal.toReal` 适配 → Gap 1/2 的 `ℝ` 形式；此时它们只是常数来源，Gap 仍为 named 缺口（`abcbridge:Cor312EpsilonArithmeticComparison.twoNamedGaps`）。

## 审计提醒
- 端口化目录存在重复拷贝（flt/flt_core/flt_test）与 `import_chain.md` 记录；引用前用当前 `.olean` 是否存在确认可 import。
- 所有外部项目结论层（含 REQUEST/(P)）按待审计数据处理，不作证据。
