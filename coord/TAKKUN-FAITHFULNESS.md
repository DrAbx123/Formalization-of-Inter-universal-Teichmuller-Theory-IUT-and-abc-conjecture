# TAKKUN-FAITHFULNESS — Takkun-IUT_LEAN 对象层保真审计（A500）

generated: 2026-11-11 05:45 (lattice，只读审计；未改 Takkun/移植文件)

来源: `tmp/external/Takkun-IUT_LEAN`（68 文件/37 模块，被移植到 `tmp/sheaf/takkun/IutLean/` 并入队 69 条）; 同仓库的 promachina（200 文件，1 sorry）、iut4-sec1、PriestAmbrose 均为 IUT 相关项目。**只采纳其对象定义/已验证引理；其结论（含 REQUEST 的 (P)）作为待审计数据。**

## 0) 总判定（写死）

1. Takkun 的整体架构是 **“对象骨架 + 诚实数据模式 + 部分真实算术”**，不是完整 IUT 对象构造。其 `SORRY_LEDGER.md` 声称 `opaque 0 / sorry 0 / axiom 0`，但多数“opaque 解消”是把 opaque 命题**替换为数据模式/轨道定义/恒真命题**，而不是构造出对象。
2. **`MultiradialRepresentation` 不是具体对象**：仓库中没有 `structure/def MultiradialRepresentation`（仅 docstring 提及）；主不等式被“保留为 `MultiradialRepresentation`”，实际落到 `Multiradial/Cor312.lean` 的 **`PilotVolumeData` 数据结构 + `containment` 字段**，`cor312` 是条件定理。所谓“主定理”well-definedness 只是 `multiradialOutput x := orbit Γ x` 的轨道定义（恒真）。
3. 因此：**Takkun 的 Cor 3.12 / Thm 1.10 结论不能计入 3.12 进度**；其真内容 = `PilotVolumeData.containment`（Thm 3.11↔3.12 桥）+ `Thm311Transcription.hull_bound` + `MultiradialSupply`（算术实现）+ REQUEST 的 **(P)**，均为 named gaps / 待审计数据。
4. 真实资产是 **辅助数学**（p 进 exp/log、不同上界、局部域、连续上同调、椭圆曲线、组合/群论、Mathlib Galois 范畴），以及 `Arithmetic/RealHodgeTheater`/`RealFrobenioid`/`RealKummer` 的**部分真实实例**（真实 `ℚ̄_p`、Galois 群、谱范数、q=11、θ=11^{j²}），后者作者本身诚实列出“仍骨架”的部分。

## 1) 对象层逐文件/模块判定

| 模块/对象 | 判定 | 证据（file:decl） | 说明 |
|---|---|---|---|
| `Multiradial/MainTheorem.lean` — “MultiradialRepresentation” | **骨架/数据模式** | 无 `structure/def MultiradialRepresentation`；`theorem multiradialWellDefined`；`def MultiradialWellDefined (D) := ∀ x g, D.multiradialOutput (g•x)=D.multiradialOutput x` | 主不等式未证明；well-definedness 来自 `multiradialOutput := orbit` 的定义，**恒真**（`output_eq_of_indeterminate` 用 `MulAction.orbit_eq_iff`）。 |
| `Multiradial/Cor312.lean` — `PilotVolumeData` / `cor312` | **骨架/数据模式（条件定理）** | `structure PilotVolumeData`（Ω/Γ/vol/vol_mono/thetaPilot/qPilot/hull/hull_spec/**containment**）；`theorem cor312 : P.negLogQ ≤ P.negLogTheta` | 唯一深输入 = `containment : ∃ g, qPilot ≤ g•thetaPilot`（作者注明 = Thm 3.11(iii) 到 Cor 3.12 的桥/争议点）；`cor312` 条件于该字段，不是 IUT 结论。 |
| `LogTheta/Indeterminacy.lean` — Ind1/2/3 与多輻输出 | **骨架（轨道模型）** | `def UpperSemiCompatibility := ∀ x g, g•x ∈ orbit Γ x`（轨道定义下**恒真**）；`structure LogShellIndeterminacy`；`def multiradialOutput := orbit`；`theorem upperSemiCompatibility` | (Ind3) 真上半両立性被作者自己称为“轨道模型的忠实近似”；本审计判定为 ④ 简化/占位（数据模式），非真实 log-Kummer 上半両立性。 |
| `LogTheta/LogShell.lean` — LogShell/LogLink/LogChain | **骨架** | `structure LogShell where carrier : Type [AddCommGroup]`；`structure LogLink (U) (S) where logMap : Additive U →+ S.carrier` | 只记录“一个加法群 + 一个加法同态”，没有 p 进 log-shell 的壳半径/整结构/紧性/体积；真实 p 进壳在 `Padic/LogShellRadius` 等辅助模块。 |
| `HodgeTheater/Defs.lean` — Additive/Multiplicative/Full | **骨架（作者明说“组合的骨格”）** | `structure AdditiveHodgeTheater`（l、primeStrips : PrimeStripSystem l）；`structure Full`（add/mul/glue : add.l=mul.l） | 只保留组合骨架（素数 l、对称性、标签、prime strip 数据），不是 IUT 的几何 D-Θ±ell/ΘNF Hodge 剧场。 |
| `HodgeTheater/PrimeStripData.lean` — `PrimeStripSystem` | **数据模式（honest）** | `structure PrimeStripSystem`：V、addSystem/mulSystem : LabeledPrimeStripSystem、gaussian、glue（DhPrimeStripEquiv）；`structure DhPrimeStrip/FhPrimeStrip/GaussianPrimeStrip` 在 Frobenioid/PrimeStripSystem | 字段为抽象类型/作用/同构数据；没有从数域/曲线构造出 prime strip system。`Models.trivialPrimeStripSystem` 是 Unit/PUnit/ofAdd 1 的玩具 witness。 |
| `Models.lean` — 具体模型 | **骨架/玩具模型** | `def trivialPrimeStripSystem (l)`：V:=Unit、Π/G:=PUnit、qParam:=Multiplicative.ofAdd 1、glue refl；`def modelHodgeTheater : Full`（l=5, trivial strips）；“旧 opaque の下では構成不可能だった Full Hodge 剧场が実際に構成できる” | 只证明数据结构**非空/无矛盾**，非 IUT 对象实例；作者自称“抽象構造の具体モデル”。 |
| `InitialThetaData/Defs.lean` — InitialThetaData | **数据模式 + 部分真实** | `structure InitialThetaData`：F 数体、E Weierstrass、l、稳定归约/ SL2/模体/K-core 等字段；`Deferred.lean` 声称 opaque 全部具体化 | 数域/椭圆曲线/l 是真实 Mathlib 对象；但稳定归约、SL2 像、K-core、V 切断等只是**谓词字段/数据模式**；没有从具体 E 构造实例。 |
| `Anabelian/CoreData.lean` — KCoreData | **数据模式** | `structure KCoreData`（Loc 范畴/对象 C_K,X_K/覆盖/deck 作用/终对象性）；`def trivialKCoreData`（2-object Loc 模型，witness） | 数据模式 + 玩具 witness；真实 E 的覆盖范畴未构造；`CurvePi1.lean` 只是 Mathlib Galois 范畴基础上的 π1 基础。 |
| `Frobenioid/Basic.lean` — LocalMonoid/Model/degree | **半真实（代数骨架）** | `structure LocalMonoid`（Otri CommMonoid）、`valueMonoid=Associates`、`structure Model`（deg : valueMonoid →* Multiplicative ℝ）、`degree_mul` 等 | 是真实的抽象代数定义/引理（Mathlib-backed），但不是 IUT 的实际 Frobenioid；无函数体/除子/上同调结构。 |
| `Multiradial/Thm311.lean` — Thm311Transcription | **部分真实 + 单个 named 义务** | `degree_unit_mul_pow`、`gaussian_total_degree`、`theta_vol_derivation`（真实整数/实分析计算）；`Thm311Transcription` 的 `hull_bound` 义务 | 作者诚实声明“Thm 3.11 转录完全归约到 hull_bound 一点”；(Ind1)/(Ind2) 取 trivial，作者注明这是 honest 简化。 |
| `Multiradial/TwoSidedLink.lean` | **诚实分析（meta）** | `structure ThetaLinkComparison`（Send/Recv 分离、volS/volR 分离）；`relabeling_vacuous`（同一视 ⇒ 空转）、`link_not_isometric`、`strict_collapse`、`TwoSidedSupply` | 不是 IUT 对象；是对“两个 ℝ 的同一视”的形式化 trilemma；支持我们的 A497 空转判定。 |
| `Multiradial/{DisputedCore,IdentificationAudit,ThetaHullDichotomy,TranscriptionDegeneracy}.lean` | **诚实分析（meta）** | `StrictPilotData`/`strict_collapse`/`hull_exceeds_orbit`/`MultiradialSupply`；`identifiedTranscription_universal` 等 | 形式化争议与退化；明确“同一视 route 恒真、信息零”、“非同一视 route 的供给 = 算术实现”；结论不证明 IUT。 |
| `Arithmetic/RealHodgeTheater.lean` | **部分真实实例** | 真实 `ℚ̄_p`、`G_p=Gal(ℚ̄_p/ℚ_p)`、真实 q=11、θ=11^{j²}、非退化性证明；作者列“仍骨架”：Π=G、对称化 refl、Mon=ℚ̄_p^×、无阿基米德 | 是唯一有“真实局部 Galois 群 + 实际代数闭包”的 Hodge theater 实例；仍非完整 IUT 剧场。 |
| `Arithmetic/RealFrobenioid.lean` | **部分真实实例** | `integralUnits p = {u : ℚ̄_pˣ | ‖u‖ ≤ 1}`、`realFrobenioid p : Frobenioid.Model`（deg=−log‖·‖）、`degree_qFrob`、`real_theta_vol_11a3` | 抽象 Frobenioid 论与真实 ℚ̄_p 谱范数接地；但只是局部 toy 实例。 |
| `Padic/*`（PadicExp/PadicLog/LogVolume/ComplexLog/LogShellRadius/ShellTransport/RealLogKummer） | **真实辅助数学** | 真实 p 进 exp/log 收敛/等长/全射、壳半径/体积计算 | 可作为辅助引理采纳；不是 IUT 对象。 |
| `NumberTheory/*`（Places/PlaceLocalization/DifferentBound） | **真实辅助数学** | 真实素点、局部化 DVR、不同上界 | 辅助。 |
| `Cohomology/*`（Continuous/CentralExtension/Synchronization） | **真实辅助数学** | 连续上同调、中心扩张、基本类存在性（`FundamentalClass`） | 辅助；`FundamentalClass` 是结构/存在性，不是 IUT 对象。 |
| `Theta/*`（ThetaValues/ThetaGroup/MonoTheta）、`Cyclotome/*`、`Combinatorics/Fl`、`EllipticCurve/*`、`Anabelian/CurvePi1` | **真实辅助数学** | 2ℓ次根/θ 值/群作用/Mathlib 椭圆曲线/π1 基础 | 辅助引理；theta values 为真实根/幂。 |
| `Diophantine/Thm110.lean` | **条件+真实初等推导** | `cTheta_ge_neg_one`、`thm110_elementary_deduction` 条件于 `PilotVolumeData`（从而 containment）+ 明示 C_Θ；作者列剩余 (i)(ii)(iii) | 初等推导真实；IUT 结论依赖 named gaps。 |

## 2) “opaque 解消”的三种模式（审计重点）

| 模式 | 例子 | 判定 |
|---|---|---|
| (a) 替换为**恒真/轨道定义** | `multiradialOutput := orbit`；`UpperSemiCompatibility := ∀x g, g•x∈orbit` | **④ 骨架/占位**：well-definedness 恒真，不编码真实 Ind3 上半両立性。 |
| (b) 替换为**数据模式**（fields 抽象） | `PrimeStripSystem`、`HodgeTheater.Full`、`InitialThetaData`、`KCoreData`、`PilotVolumeData`、`LogShell` | **④ 数据模式**：结构存在且可实例化（trivial witness），但没有实际几何/算术实例；深内容移到“实例供给”。 |
| (c) 替换为**具体命题 + 玩具 witness** | `SixTorsionRational`、`ContainsSL2Image`、`HasValuationSection`、`IsKCore` 等；`Models` 的 Unit/PUnit/ofAdd1 | **④ 部分真实**：命题本身具体，但 witness 是 trivial；非 IUT 实例。 |

## 3) 结论与使用规则

1. **采纳范围**: 只采纳 Takkun 的**对象定义**（Frobenioid/LocalMonoid/PrimeStrip 数据模式、LogShell、部分真实实例中的定义）与**已验证辅助引理**（p 进分析、不同、上同调、群论、θ 值等）；引用时注明 `tmp/sheaf/takkun/...` 与判定等级。
2. **不得采纳为结论**: `MultiradialRepresentation`、`cor312`、`Thm 3.11 转录`、`Thm 1.10`、`Hull_bound`、`containment`、`MultiradialSupply`、REQUEST 的 **(P)** —— 均为条件/数据模式/named gap，属**待审计数据**，不计 3.12 进度。
3. **对象 gate（A499）继续有效**: Takkun 对象均为“接口/骨架/部分真实”，无对象级 `_constructed` 定理；其上层接线不得计进度。
4. **可与 TwoSidedLink/IdentificationAudit 对齐**: 其 trilemma/同一视空转分析与我们 A497 的 qTheta 空转判定一致，可作参考文献（meta），不作源对象。

## 4) 移植编译监看

- 队列: `extra-targets` 541 条，其中 `takkun` 69 条；watchdog log 中 takkun 行 = 0（截至 05:45），`.lake/build/lib/lean/tmp/sheaf/takkun` olean = 0 → 尚未开始编译。
- 移植 import 路径为 `tmp.sheaf.takkun.IutLean...`；监视 START/FAIL/DONE，按 per-file 日志迭代（不手动编译、不碰 watchdog）。
- Takkun 原仓库为 4.32.0（LANA/原环境），移植到 4.32.2 可能出现版本差异；编译失败时优先检查 Mathlib API 差异，不改其数学内容。

## 5) 附: Takkun 自述边界（可直接引用）

- `SORRY_LEDGER.md`: “opaque 0/sorry 0/axiom 0”；但自述解消方式包括“具体的数据構造化(honest データパターン)”与“インスタンス供給の将来課題”。
- `Multiradial/MainTheorem.lean` doc: “主不等式そのものは IUT 全体の帰結ゆえ `MultiradialRepresentation` として保留する”；`Thm311.lean` doc: “Thm 3.11 の転写は `hull_bound` 一点に完全還元”；`Cor312.lean` doc: “Cor 3.12 は `PilotVolumeData` のインスタンス供給に還元”。
- `REQUEST_theta_hull_derivation.md` 的 **(P)** = 受信侧 Step (v) 的 λ=ord(q^{j²}) 体積适用，是其唯一 named 输入；属待审计数据。
