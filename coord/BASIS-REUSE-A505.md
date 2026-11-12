# BASIS-REUSE A505 — 对象链需要的基础 vs 联合地基现有资产

口径：只记录对象链（O1–O12）**实际会消费**的基础引理/定义，按「已有 → 直接 import；缺 → 才手写」列。搜索范围：`tmp/external/ported`（TauCeti/Fermat/Belyi，1093 oleans）、`tmp/sheaf/takkun`（68 模块，30 oleans）、`tmp/local-cft-port`（0 oleans）、Mathlib v4.32.2、自有 `LeanFormal/IUT`。

## 0. 已做动作（本次）

- `node tools/extras_add_closure.mjs` 对 mainline 目标文件算 import 闭包并入队：`Mzk1UnifiedObjectSkeletonActual`、`Mzk1MultiradialRepresentationActual`、`Mzk1HullDetNonVacuousSynthesisActual`、`Mzk1TakkunPrimeStripAdapterActual` → closure 450，新增 392，队列 total 940。
- `Mzk1UnifiedObjectSkeletonActual` 已收窄 takkun import（去掉 `Arithmetic/IntegrationTest`，改用 `Arithmetic/RealHodgeTheater` + 本地构造 `modelLogShell/modelLogMap/modelLogLink`）。

## 1. 需要的基础清单（按对象链层次）

| # | 需要的数学基础 | 消费者（对象/文件） | 联合地基覆盖 | 结论/动作 |
|---|---|---|---|---|
| B1 | p 进域 `ℚ_p`/整环 `ℤ_p`、valuation 乘法/加法律 `v(uv)=v(u)+v(v)` | O3 log-shell、O5 σ 分解、`modelLogMap` | **Takkun `Padic/LogVolume`、Mathlib `Padic.valuation_*`**（已 import via `Arithmetic/RealHodgeTheater`） | ✅ 直接 import；`modelLogMap` 本地 6 行由 `Padic.valuation_one/mul` 证 |
| B2 | p 进对数 `logOnePlus` 与壳内收敛/体积保存 | O3 单数部分、hull 壳 | **Takkun `Padic/PadicLog`（`logOnePlus`/`logOnePlus_shell`）** | ✅ 需要时 import（目前经 RealHodgeTheater 闭包部分可达） |
| B3 | p 进 log-volume（`logVol x = Real.log ‖x‖`）、壳体积公式 | O7/O9 hull 体积、`unifiedSkeletonModel_logMap_qParam` | **Takkun `Padic/LogVolume`（`logVol`、`logShellVolFormula`）** | ✅ 直接 import |
| B4 | 壳半径参数 `aRadius/bRadius`、壳包含单调性、壳 transport | O7 hull 常数、`O2ThetaObject.hullRadii/hullShell` | **Takkun `Padic/LogShellRadius`、`Padic/ShellTransport`** | ✅ qpilot O2 已 import；我们复用 |
| B5 | 全 θ 值 `q^{j²}` 与 Gauss 指数、±1 对称 | O5 etHT、O8 det 侧 | **Takkun `Theta/ThetaValues`（`thetaValueMon`/`gaussExp`）、`Arithmetic/RealKummer`（`realThetaRootSystem`/`realThetaKummer`）** | ✅ 直接 import（qpilot `O2ThetaObjectActual` 已用） |
| B6 | 2ℓ 根体系（qroot / `realQRootSystem`）与 Kummer 类 | O5 根体系、O8 | **Takkun `Arithmetic/RealKummer`（`realQRootSystem`/`realQKummer` cocycle）、`Cyclotome/Kummer`；`tmp/local-cft-port` ContinuousKummerTheory（0 olean）** | ✅ Takkun 直接 import；cft-port 暂不用（无 olean） |
| B7 | 实曲线 11a3 的 Δ/j/q 与 Tate 局部模型 | O1/O3 实模型（`realHodgeTheater`） | **Takkun `Arithmetic/CurveInstance`（`curve11a3`）** | ✅ 直接 import（经 RealHodgeTheater） |
| B8 | 局部 Galois 群 `Gal(ℚ̄_p/ℚ_p)`、`O×µ` 作用、mono-analytic core | O1/O3 prime-strip | **Takkun `Arithmetic/RealHodgeTheater`（`realDStrip`/`realGaussianStrip`/`realPrimeStripSystem`/`realHodgeTheater`）** | ✅ 直接 import；`realConcreteLattice.core := realDStrip.G` |
| B9 | 组合 Teichmüller：`F_l`、`LabCusp±`、单純推移性 | O1/O3 Hodge theater 标签 | **Takkun `Combinatorics/Fl`、`HodgeTheater/Symmetry`、`HodgeTheater/PrimeStripData`** | ✅ `Full`/`PrimeStripSystem` 已用 |
| B10 | 整数 radical、abc 三元组、primitive additive | O12/ABC 收口（`ExplicitABCWeakening`、hcomp 之外） | **Mathlib `UniqueFactorizationMonoid.radical` + 自有 `Foundations/Arithmetic/Radical`、`PrimitiveAdditive`** | ✅ 自有已有（`ABCBridge/Statement.lean`） |
| B11 | 高度理论（`logHeight₁`、`arithmeticWeight`、`abcRationalPoint`、height-weight 比较） | O12/hcomp、`ABCFormAdditiveHeightBound` | **ported TauCeti/Fermat 无高度理论**（grep `def height/logHeight` 仅 `heightOneSpectrum`，非数值高度；0 处数值高度定义）；Takkun 无 | ❌ 联合地基不覆盖 → 保留自有 `LeanFormal/IUT/ABCBridge/Arithmetic/*`（已有）为准 |
| B12 | Haar 测度 / 全局 log-volume（literal IQ 载体、product Haar、hull 有限性） | O7/O9、R3 | **Takkun 无全局 Haar（仅 p 进标量 logVol）**；ported 无 Haar（grep 0）；Mathlib Haar | ❌ 用自有 literal `litHull/litHaar/literalGlobalIQHull_measure_lt_top` + Mathlib Haar；不手写新基础 |
| B13 | 椭圆曲线/函数域 place、adic valuation、residue field、uniformizer（Frobenioid/prime-strip 的场论层） | O1/O3 place/valuation 层（若需更具体） | **ported FLT `flt_core/Definitions/Def_DedekindDomain_AdicValuation_InlineSpecific`（`ResidueFieldEquivCompletionResidueField`、`inertiaDeg_asIdeal_completionIdeal`、`exists_uniformizer`）、`flt_core/P2M/Sol/S_AlgebraicCurve_Place_adicValuation_isRankOneDiscrete`；TauCeti `FieldTheory/FunctionField/Place/OfValuationSubring`、`RingTheory/Valuation/Center`（`heightOneSpectrum`）** | ◐ 候选可复用（函数域层，非 p 进局部域）；当前对象链暂未消费 → 记录，不 import（避免拉大闭包） |
| B14 | 函数域 Belyi radical / Riemann–Roch | O5 etHT 的 Belyi 侧（未来） | **ported `tauceti_belyi_ff/TauCeti/FieldTheory/FunctionField/Belyi/Radical`、`tauceti_rr`** | ◐ 候选（未来若走 Belyi 线再用） |
| B15 | 实分析：`Real.rpow`、`log`/`exp` 不等式、级数收敛 | O8 det、O9 体积、`ExplicitABC` | **Mathlib** | ✅ 直接 import（已有） |

## 2. 直接可 import 的具体模块（已确认存在）

- Takkun：`tmp.sheaf.takkun.IutLean.Padic.LogVolume`、`...Padic.PadicLog`、`...Padic.LogShellRadius`、`...Padic.ShellTransport`、`...Theta.ThetaValues`、`...Cyclotome.Kummer`、`...Arithmetic.RealKummer`、`...Arithmetic.RealHodgeTheater`、`...Arithmetic.CurveInstance`、`...Combinatorics.Fl`、`...HodgeTheater.PrimeStripData`。
- Ported（候选，未消费）：`tmp.external.ported.flt_core.Definitions.Def_DedekindDomain_AdicValuation_InlineSpecific`、`tmp.external.ported.flt_core.P2M.Sol.S_AlgebraicCurve_Place_adicValuation_isRankOneDiscrete`、`tmp.external.ported.tauceti2.TauCeti.FieldTheory.FunctionField.Place.OfValuationSubring`、`tmp.external.ported.tauceti2.TauCeti.RingTheory.Valuation.Center`、`tmp.external.ported.tauceti_belyi_ff.TauCeti.FieldTheory.FunctionField.Belyi.Radical`。
- 自有：`LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison`、`LeanFormal.IUT.Foundations.Arithmetic.Radical`、`...PrimitiveAdditive`、literal IQ carrier/`litHaar` 系列。

## 3. 仍缺、必须自写（联合地基完全不覆盖）

1. **数值高度–算术权比较**（B11）：`abcRationalPoint` 的 `logHeight₁ ≤ (1+ε)·arithmeticWeight + A` 类型引理；port/Takkun 都没有（Takkun 的 `heightOneSpectrum` 只是 valuation spectrum）。自有 `ABCBridge/Arithmetic` 已有，继续用。
2. **全局 Haar/log-volume 归一化**（B12）：literal IQ 载体上 product Haar 与 procession 平均（自有 `litHaar`、`HaarTranslateRealLineProcessionAverage` 已有；缺的是把 Takkun `Padic.logVol` 与全局归一化桥接的引理）——桥接引理需自写（短，`_constructed`）。
3. **k=11 的本地 O3 模型 glue**：自有 `gaussianHodgeTheater` 与 Takkun `realHodgeTheater` 的连接（`PrimeStripSystem` 的 `glue/nondegenerate` 字段）需一条真实适配引理（当前仅并列，未建同构）。

## 4. 与 A505 策略的一致性

- 已复用：B1–B9 全部来自 Takkun/Mathlib，未手写；B10/B15 自有/Mathlib。
- 未抢占 ported 基础：B13/B14 记录为候选，不 import（其函数域层不是当前对象链消费者；避免无谓闭包）。
- 自写范围仅 B11–B12 的桥接与 O3 适配（真实对象、`_constructed`），符合「只造真正缺的对象」。