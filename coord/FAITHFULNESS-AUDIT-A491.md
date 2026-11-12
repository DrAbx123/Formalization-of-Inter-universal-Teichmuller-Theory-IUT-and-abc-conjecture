# FAITHFULNESS-AUDIT-A491 — LANA 移植与 NumericalWall 保真审计

generated: 2026-11-11 05:30 (lattice, 主持)

方法: 只读核对源码定义/结构字段/定理陈述（`tmp/sheaf/lana/iut/Iut`、`tmp/sheaf/xif/paper`），未编译；以 LANA 模块 docstring（尤其 `Wall/Checks.lean` 自述）为原始语义参照。判定词表: ①忠实 ②过强 ③过弱 ④占位/简化 ⑤未定义。

## 0) 审计对象与状态（olean 口径，2026-11-11 05:29）

| 文件 | olean | queue |
|---|---|---|
| tmp/sheaf/xif/paper/A490WallNumericalAlignmentActual.lean | False | True |
| tmp/sheaf/xif/paper/A490WallThetaShiftAlignmentActual.lean | False | True |
| tmp/sheaf/xif/paper/Mzk1LANAQPilotWallRegionActual.lean | False | True |
| tmp/sheaf/lana/iut/Iut/Wall/NumericalWallHullActual.lean | False | True |
| tmp/sheaf/lana/iut/Iut/Wall/NumericalWallRssActual.lean | False | True |
| tmp/sheaf/lana/iut/Iut/Wall/NumericalWallActual.lean | False | True |
| tmp/sheaf/lana/iut/Iut/Wall/SSIneqOfStep3115Actual.lean（附加） | False | True |

注: 以上均 0 sorry、无 IsTrivial/trivialAlg（`NumericalWallActual`/`SSIneq` 的 True 仅出现在 docstring “No ... True placeholder”）。

## 1) 逐项保真判定

### (a) ValBPS — `tmp/sheaf/lana/iut/Iut/Wall/BPS.lean:175`

- 定义: `structure ValBPS (V) (bad)` 字段 `C : Type`（`AddCommGroup`+`Module ℝ`+`finrank ℝ C = 1`）、`localPilot : V → C`（逐点非零）、`pilot := ∑ v ∈ bad, localPilot v`（非零）；`sumMap : (V →₀ ℝ) →ₗ C`，`PF := ker sumMap`；`eta (x) := x • pilotCoord`，`eta_pilot : eta x pilot = x`，`pilotCoord` 由 `pilot` 非零构造。
- **C**: **① 忠实（value-level）**——论文 value portion 在 LANA 中层化为带 pilot 的 1 维实向量空间；字段齐备（1 维、pilot 非零）。**④（相对 paper 实际 value group）**——C 是抽象实线，不是由数域/赋值的实际值群构造。
- **localPilot / pilot**: **④ 占位/简化**——`localPilot` 是任意 `V → C` 的非零向量族，没有从 p-adic 赋值/ℓ-进 Tate 参数构造；“`pilot = Σ localPilot`”只复制了 φ_C 的形式，数值内容未定义。
- 结论: ValBPS 作为 LANA value-level interface = ①；作为 paper value portion 的忠实构造 = ④。

### (b) EtaAlg 的 T1–T3 — `tmp/sheaf/lana/iut/Iut/Wall/EtaAlg.lean:96`

- 字段: `model : Pl D → GMData`（opaque）、`Side`（opaque，仅 `Nonempty`）、`etUnit : Side → EtUnitBPS model`、`out : ∀ {B} {h}, BPS.Iso B ⟨etUnit h, thetaValD⟩ → Ind3 D → Region D`（opaque 函数，无算法步骤）、`ind12_acts_on_S`（T1）、`etUnitOnly`（T2）、`realisation`（T3）。
- **T1 (ind12_acts_on_S)**: **③ 过弱**——只断言对每个 `α : EtUnitIso B.et B.et` 存在某个 `τ : Ind3 D ≃ Ind3 D` 使 `out ((α,refl).trans ι) S = out ι (τ S)`；没有 `τ` 的群作用/函子性/与 Θ-link/Ind2 兼容律，无法编码论文的 (Ind1),(Ind2) 作用。
- **T2 (etUnitOnly)**: **① 忠实（方向）**——输出只通过 étale-unit 部分依赖，匹配 LANA §6.2(ii)/Remark 6.2.2；但仅存在性 `∃f`，无唯一性/自然性（次要 ③ 注记）。
- **T3 (realisation)**: **② 过强**——对**每个**输出断言 `IsAdelic D (out ι S) ∧ InHullOfImage D (out ι S)`；这是论文 IUT III Thm 3.11(ii)/Cor 3.12 的 hull/realisation 内容，作为 interface 字段把目标侧结论嵌入了假设。结合 `Wall`（η^anab=η_q）即可平凡推出 variant（LANA `Checks` 自述 numericalWall_iff 是 restatement/circular）。
- **EtaAlg 整体**: **④ 简化 interface**（η-algorithm 的算法本体/构造未形式化；`out` 是 opaque field，T1–T3 是性质公理）。**⑤ 未定义**（作为“η-algorithm”本身没有定义/构造）。

### (c) concreteVariantData — `tmp/sheaf/lana/iut/Iut/Concrete/ThetaRegion.lean:359`

- `Corollary312VariantData := { data : InitialThetaData, qPilot : QPilotData data, rhsData : RHSData data }`；`Corollary312Variant X := X.qPilot.lhs ≤ X.rhsData.rhs`。
- **qPilot**（`Cor312/LeftHandSide.lean:58`）: `badFinset` + `badFinset_spec : ↑badFinset = badPlacesOver …`、`weight`（`concreteVariantData` 取 `inertDeg w / finrank ℚ F`）、`logQ := ∑ w∈bad, weight w * (qOrder … : ℝ) * log(residueChar w)`、`absLogQ := logQ/(2ℓ)`、`lhs := -absLogQ` → **① 真实构造**（由 D 的坏位点/惯性次数/q 阶定义；结构字段 `weight` 本身允许任意正函数，但 concreteVariantData 用 inertDeg 实例化）。
- **rhsData**（`Cor312/RightHandSide.lean:65`）: `container`（`LocalTheory.container`，tensor packets/local constructs）、`vol : LogVolumeData`、`hull : ContainerHullSystem`、`thetaPilot`（`D.thetaPilotOn`，2ℓ-th roots/Tate 参数）、`rhs := processionVol hull(thetaPilot)` → **① 真实 Lean 构造**（经 LocalTheory 模型层，见 d 注）。
- **concreteVariantData**: **①**（`data/qPilot/rhsData` 全部由 D 具体实例化）。

### (d) Rss / etaQ / rssEquiv / qPilot.lhs

- `Rss := Quotient (Setoid.comap logVol ⊥)`（`Wall/Rss.lean:446`）；`rssEquiv : Rss D ≃ ℝ := Equiv.ofBijective Rss.logVol`，满射由 `logVol_surjective`（`archScale (exp x) integralRegion`）给出；`Rss.mk`/`logVol_mk`/`mk_eq_mk_iff`。
- **Rss / rssEquiv**: **④ 简化**——论文 `R_ss` 是 realified Frobenioid 的 value group；仓库把它定义为“admissible regions 按 log-volume 相等的商”，再用 `rssEquiv` 与 ℝ 等同。LANA docstring 明确这是 modelling choice；因此不是 paper-faithful 对象（对 LANA 内部 = ①）。
- **etaQ**: **①**——`etaQ := (qVal D.bpsDegrees).eta D.qPilot.lhs`（`Rss.lean:501`），把 value BPS 的 pilot 送到 q-pilot lhs；`etaQ_bijective`（需 `lhs_neg.ne`）。`logVol_etaQ_pilot` 是**按定义的归一化**（由 `etaQ`/`rssEquiv` 构造），不是关于 paper 的独立定理。
- **qPilot.lhs**: **①**——见 (c)，是 q-divisor 的显式实数值 `-|log q|`（`logQ/(2ℓ)`）。
- 注: `qVal D.bpsDegrees` 的 `ValBPS.C` 继承 (a) 的抽象；`etaQ` 的忠实性受 (a)/(d) 的 modelling choice 限制。

### (e) 我们 5 个桥接文件的假设强度

| 文件 | 假设 | 结论 | 强度判定 |
|---|---|---|---|
| ① A490WallNumericalAlignmentActual | `EtaAlg`（T1–T3）+ `Wall D A`（∀h₁h₂ Θ-link ∃ι,S, η^anab=η_q） | `NumericalWall D`；`Corollary312Variant`（经 numericalWall_iff） | **② 过强（作为 rung/证据）**: Wall 是 η^anab=η_q 的全局形式，LANA 自述与 variant 互为 restatement；条件定理本身有效，但没有独立数学内容。 |
| ② A490WallThetaShiftAlignmentActual | `Wall` + `A.ThetaShift`（identified-copies logVol 律，`MultiContainer:105`） | ∃ Ind3 满足 `-s|log q|+logVol(S)=qPilot.lhs`；`wall_region_logVol_eq_qPilot` | **②/③**: ThetaShift 是额外显式假设（比 Wall 多）；结论只是 logVol 等式（**③ 过弱**，未给 Rss.mk 等式/InHullOfImage）。 |
| ③ Mzk1LANAQPilotWallRegionActual | 无额外数学假设（用 LANA qRegion/scale 事实） | `numericalWall_iff_rss_qPilotScale`（Rss 字段写成 `symm(-qPilotScale)`）；`QPilotRegionWallData` | **①**: 与 `numericalWall_iff_rss` 字段一一对应，仅重参数化（`qPilot_lhs_eq_neg_scale`）；不引入强假设。 |
| ④ NumericalWallHullActual | 无额外假设；存在性定理显式 `hx : x ≤ rhs` | `NumericalWall ↔ ∃U IsAdelic∧InHullOfImage∧logVol=qPilot.lhs`；`x≤rhs ⇒ ∃U`（archScale） | **①（归约）**: eta 等式与 logVol 等式逐字段对应；`hx` 是显式条件（等于目标不等式的 ≤ 侧）。 |
| ⑤ NumericalWallActual | `NumericalWallInput := qPilot.lhs ≤ rhsData.rhs`（explicit named input） | `NumericalWallInput ↔ NumericalWall`；`↔ Corollary312Variant`；`numericalWall_holds_of_input` | **⑤ 显式 named 缺口**: input 恰是 Cor 3.12 variant 的实不等式本身（既非过强也非过弱，但**未证明**）；无 hidden axiom/True。`numericalWall_holds_of_qPilotRegion_inHull` 的 `InHullOfImage(qPilotWallRegion)` 是 sufficient-only（doc 明示，`qPilotRegionInHull_implies_input`），强于 named input，不作为主输入。 |

- 关键: ①–⑤ 的定理全是 **等价/重述/条件蕴含**，没有一个在无 Wall/ThetaShift/InHullOfImage/named input 的前提下构造 `NumericalWall`。
- 交叉核对 mainline 自述: `NumericalWallActual` 的 `numericalWallInput_iff`/`_iff_variant` 方向正确（`.trans` 链）；文件 doc 明示 “remaining inequality is explicit named hypothesis”。

### (f) 全仓占位/兜底扫描（case-sensitive）

- 5 个桥接文件 + RssActual + NumericalWallActual: **True/PUnit/IsTrivial/trivialAlg = 0**（NumericalWallActual 的 “True” 仅在 doc “No ... True placeholder”）。
- `tmp/sheaf/lana/iut/Iut` 全树: `\bTrue\b` **7 hits / 7 files**:
  - `Cor312/RationalPlace.lean:41 | finite _ => True`（函数值，非命题假设）；
  - `Cor312/ThetaData/Places.lean:39 | Sum.inl _ => True`（同上）；
  - `WallEquiv/NonDerivable.lean:422 Adelic _ := True` —— 属于“prescribed numbers”**反例/toy 模型**（用于 non-derivability），非 paper 对象（④）；
  - `Tripod/Basic.lean:336 Hyperbolic _ := True` —— tripod `HeightTheory` 模型字段（④ 简化）；
  - `Wall/MultiContainer.lean:301 Wall3 := WallOn fun _ _ => True` —— 用全关系编码 “all pairs wall”（④ 建模方式，不是假证明）；
  - `Wall/SSIneqOfStep3115Actual.lean:30`、`Wall/NumericalWallActual.lean:27` —— doc 中的 “True placeholder” 字样。
  - 结论: 上述 True 均为**显式 simplified model/关系编码/文档**，没有藏在 5 个桥接文件或 NumericalWall 主链的假设里；但 `Adelic := True`/`Hyperbolic := True` 属 ④，审计表保留。
- `PUnit`: **3 hits / 2 files** —— `Frobenioid/Global.lean`（`Discrete PUnit` 作 point category）、`HodgeTheater/PrimeStrip.lean`（`gmOf PUnit`）；属建模对象（point/unit type），非兜底证明。
- `Subsingleton.elim`: **29 hits / 17 files**，抽查 `Concrete/LocalConstruct/{LogShell,Packet,Integral}.lean`、`Frobenioid/{Global,PAdic}`、`Anabelian/Genuine/Theory.lean` 等，均为 subsingleton 结构/证明无关性（如 hom subsingleton、unit 结构），未发现用其伪造非平凡等式；建议在目标闭包复核时逐条列入 checklist（审计无 veto）。
- `IsTrivial`/`trivialAlg`: 仅 `Wall/Checks.lean`（显式 trivial instance/`exists_isTrivial_iff`）与 `Wall/IdentifiedCopies.lean`（`not_isTrivial_of_lgpLaw`）；**未被桥接文件使用**，且 trivial instance 被 lgpLaw 排除。

## 2) 结论（写死）

1. **`NumericalWall D` 未被证明**。现有全部相关定理都是：① `numericalWall_iff : NumericalWall ↔ Corollary312Variant`（LANA 自述 restatement/circular）；② `numericalWall_iff_rss`（R_ss class 重述）；③ `numericalWall_iff_rhs_ge_lhs : NumericalWall ↔ qPilot.lhs ≤ rhsData.rhs`（把 wall 归约为单个实不等式）；④ 条件定理（Wall⇒、ThetaShift⇒、InHullOfImage(qPilotRegion)⇒）。**没有任何无假设构造满足 NumericalWall 的 adelic/hull region**。
2. **`NumericalWallInput`（`(concreteVariantData D).qPilot.lhs ≤ (concreteVariantData D).rhsData.rhs`）是显式 named 缺口**：它恰是 Cor 3.12 variant 的实不等式，已形式化为 Prop/definition（`NumericalWallActual.lean:58`），并由 `numericalWallInput_iff` 与 wall 等价、由 `numericalWallInput_iff_variant` 与 variant 等价；不是 hidden axiom/True，也**不是已证事实**。
3. 迁移对象中，(a) C 忠实但 localPilot/pilot 为抽象；(b) EtaAlg 的 T1 过弱、T3 过强、整体是 interface 而非 η-algorithm 本体；(c) concreteVariantData 是真实具体构造；(d) Rss/rssEquiv 是简化 modelling（LANA 明示），etaQ/qPilot.lhs 本身定义忠实；(e) 5 桥接中 ③/④ 忠实归约，①② 假设过强/过弱，⑤ 是显式 named 缺口；(f) 桥接文件无 True/PUnit 等兜底，LANA 树中少数 True 是显式 toy/model/文档，需要在最终 gate 复核时作为 ④ 记录。
4. 建议: 把 `NumericalWallInput` 写进 DAG-BLOCKED 类“显式 named 缺口”（不是 obstruction，是目标不等式）；任何后续“NumericalWall proved”声明必须给出该 inequality 的证明或新构造，不能引用 `numericalWall_iff*` 系列作为证明。

## 3) A496 归档（reference-only）

- A496 决定: LANA 模型不再作接线/目标（ValBPS 抽象、EtaAlg opaque/T3 过强、Rss modelling、2ℓ 归一化差、True toy 模型）。本审计的 LANA 部分降级为 **reference-only**，保留作源码/写法参考。
- LANA 移植文件已全部移出 watchdog 队列（queue 466、lana-lines=0）；主链改以我们自己的对象/陈述为准，见 `coord/MAIN-CHAIN-AUDIT-A496.md`。
- **NUMERICAL-WALL-PLAN 的 NumericalWall 路线不再推进**；`NumericalWallInput` 记为显式 named 缺口（非 obstruction），不得作 rung。

