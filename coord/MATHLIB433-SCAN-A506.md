# MATHLIB v4.33.1 SCAN（A506）——可用性与候选 API 清单

## 0. 结论先行（诚实）

- **本机没有 v4.33.1 的 mathlib 源码可在 v4.32.2 主构建里扫描**：`tmp/external/flt-lean/lean-toolchain = leanprover/lean4:v4.33.1`，`lake-manifest.json` 固定 mathlib rev `db584cd6d46c92f209a44c0f1c829460d327499d`，但 `tmp/external/flt-lean/.lake/packages/` **不存在**（无 mathlib 源码、无 olean）。
- `~/.elan/toolchains` 已装：v4.30.0、v4.31.0、v4.32.0、v4.32.2、v4.33.0、v4.36.tmp —— **没有 v4.33.1**，因此即使拉到源码也无法用 v4.33.1 编译验证。
- 其他外部项目同样无 v4.33.1 mathlib：`com-junkawasaki-iut-lean`（v4.33.0-rc1）无 `.lake/packages`；`iut4-sec1` mathlib=v4.32.0；`Takkun-IUT_LEAN` mathlib=v4.31.0；promachina 的 `.lake/packages/mathlib` 无 lean-toolchain（不完整）。
- 故本轮**未执行任何 cherry-pick**（无源码可 diff），也未改主构建；下面给出「拿到源码后」的扫描/移植方案与候选 API 清单。
- 转码工具 `tools/transcode_lean_432.mjs` 已就绪（外部较新源码 → 4.32.2 语法：去 `module`/`public import`/`public` 前缀）；takkun 移植已跑过。若我的对象文件 import 的 takkun 模块有语法/版本报错，先用该工具处理对应外部源码副本再重排，**不升级工具链**。

## 1. 获取 v4.33.1 源码的两条路径（供决定，不擅自执行）

1. `cd tmp/external/flt-lean && lake update`（或 `lake exe cache get`）：需要网络 + v4.33.1 toolchain（`elan toolchain install leanprover/lean4:v4.33.1`）。mathlib4 rev `db584cd6` 的源码 ~数百 MB；**不需要**在我们主构建里编译全部 10k oleans——只把命中模块 copy 到 `tmp/newmathlib/` 用 v4.32.2 适配编译。
2. 若用户/lead 提供 mathlib433 源码目录（任意路径），我可用脚本扫描：`git -C <m433> diff --name-only <v4.32.2 对应 commit>..db584cd6` + 对本文件 §2 关键词 grep，输出候选文件清单后再人工 cherry-pick。

## 2. 对我们对象层可能有用的 v4.33 新 API 方向（待源码验证）

按对象链层次列「希望被简化」的 API；每项标注当前 v4.32.2 的替代写法（若已有则不急着升级）。

| # | 对象链需求 | 当前 v4.32.2 写法（自有/Takkun） | v4.33 候选新 API（搜索关键词） | 消费者 |
|---|---|---|---|---|
| N1 | prime-strip 的 monoid/子幺半群生成 | `Submonoid.closure (Set.range thetaValueGenerator)`；`LGPMonoid.splittingMonoid_eq_closure` | `Submonoid.closure_*`、`MonoidHom.range`、`Submonoid.map/comap` 新引理 | Takkun `SourceLGPMonoidLayer`、自有 prime strips |
| N2 | prime-strip 同构的群律/复合 | 手写 `refl/symm/trans`（Takkun `DPrimeStripEquiv`、`FPrimeStripEquiv`；自有同） | `MulEquiv`/`Equiv` 的 `trans_assoc`、`toEquiv_inj`；`CategoryTheory.Iso` 简化 | prime-strip 链、unified skeleton |
| N3 | log-shell 的加法群/紧性 | `LogShell.carrier : Type u` + `[AddCommGroup]`；紧性未编码 | `CompactlyGeneratedSpace`/`ProperSpace` 新实例、`Bornology.IsBounded` 新引理 | log-shell、hull 紧性 |
| N4 | p 进 valuation/log | `Padic.valuation_one/mul`、`Padic.valuation_p`、`Padic.logOnePlus` | `Padic.valuation_*` 新引理、`Padic.norm_*`、`Padic.log_*` | `modelLogMap`、`O2ThetaObject` |
| N5 | Haar/体积归一化 | `MeasureTheory.Measure` + 自有 `litHaar`；`ENNReal.toReal` 手算 | `MeasureTheory.Measure.restrict_*`、`lintegral_*`、`ENNReal.toReal_*`、`Measure.IsFiniteMeasure` 新引理 | R3 hull 有限性、log-volume |
| N6 | `Real.rpow`/`Real.log` 单调与代数 | `Real.log_le_log_iff`、`Real.rpow_nonneg` 等手选 | `Real.rpow_le_rpow`、`Real.log_le_log`、`Real.exp_le_exp` 新变体 | `ExplicitABC`、det 归一化 |
| N7 | `Finset.prod`/`prod_pos`/`prod_congr` | 直接用（`packetDet_eq_prod`、`Finset.prod_pos`） | `Finset.prod_le_prod`、`Finset.prod_bij` 新引理 | packet hull 体积 |
| N8 | 商/Setoid 提升（orbit 输出、Rss） | `Quotient.lift`、`Setoid.comap`（自有 R4/literal） | `Quotient.liftOn'`、`Setoid.ker/comap` 新引理 | multiradial orbit、Rss |
| N9 | 线性代数 tensor packets | `TensorProduct` + `LinearEquiv` 分布（Takkun `tensorPacketEquiv`） | `TensorProduct.assoc/congr`、`PiTensorProduct` 新 API | O2/O3 tensor packet |
| N10 | 椭圆曲线 Tate/局部模型 | Takkun `Arithmetic/CurveInstance` 手算 `curve11a3` | `WeierstrassCurve`、`EllipticCurve` 新 API（v4.33 可能有 Tate 参数/约化引理） | O1 实模型 |

## 3. 若拿到源码的执行步骤（脚本化）

1. 生成 diff 文件表：`git -C <mathlib433> diff --name-only <ours>..<db584cd6> > tmp/m433-diff-files.txt`；
2. 关键词过滤：`Submonoid\.closure|MulEquiv|Padic\.valuation|Measure\.restrict|ENNReal|Real\.rpow|TensorProduct|Weierstrass|Quotient\.lift|IsBounded|CompactlyGenerated`；
3. 对命中文件的 `theorem/lemma/def` 名单与 v4.32.2 同名比对：新增名 → 候选 cherry-pick；改签名 → 需适配；
4. cherry-pick 到 `tmp/newmathlib/`（每文件保留 license 头 + 来源 commit），用 v4.32.2 编译；只 import 命中模块的闭包（`extras_add_closure.mjs`）；
5. 每个 cherry-pick 必须由一个**实际消费者**（本清单 N#→对象文件）引用，否则不入队。

## 4. 当前行动

- 无可扫描源码 → 本轮不 cherry-pick、不改主构建（符合「不整体升级」策略）。
- 已有 v4.32.2 下可用替代（N1–N10 均有现写法），对象链不被阻塞；如需 v4.33 简化，先按 §1 路径 1 获取源码或由 lead/用户提供源码目录。
- 已记录本清单；下次拿到源码时按 §3 自动扫描。