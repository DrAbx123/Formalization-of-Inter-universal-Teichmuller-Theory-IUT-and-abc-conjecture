# P8 组装依赖清单审计（andrew, 2026-11-17 19:10）

目的：在 P8 全链收口前暴露隐藏缺口；**本审计不计闭合**，所有显式参数/条件接口按待消义务记账。

## 0. 出口链（已 DONE，三公理）

| 声明 | 文件/时间 | 状态 |
|---|---|---|
| `p8_input_of_all (H : ∀ε>0, P8AssemblyInput ε) : P8UniformHeightBound` | `Mzk1G1P8WiringActual` 00:28:57 | DONE |
| `p8_assembly_actual (H) : ABCConjecture` | 同上 | DONE |
| `abc_of_p8 (h : P8UniformHeightBound) : ABCConjecture` | 同上 | DONE |
| `P8AssemblyInput`/`routeF9_all_of_assembly`/`freyJProductCriterion_of_routeF9`/`p8UniformHeightBound_of_assembly`/`abcConjecture_of_assembly` | `Mzk1G1P8ProducerAssemblyActual` 22:03:14 | DONE（骨架） |
| `p8_abc_of_uniformHeightBound_actual` | `Mzk1P8ActualDisplayHeightActual` | DONE（accepted） |
| `abcConjecture_iff_freyJProductHeightCriterion` | accepted `ABCEllipticHeightCriterion.lean:61` | DONE（accepted） |

`P8AssemblyInput` 字段：`n δ C6 C7 C8 C9 heps hδ hn hδ_n perTriple`；`perTriple` 每 ABC 三元组给出
`(hOmega, DL, hPi)` 与 F6/F7/F8/transport 的四个界。P8 组装本身已 DONE，**缺口全在 perTriple 的输入来源**。

## 1. perTriple 四类输入

### 1.1 hOmega（D1 侧 q-height 界）
- 消费：`D1AnalyticInput.upper_estimate`（`Mzk1G1D1ProducerActual` 21:11:19 DONE，conditional on D1AnalyticInput）。
- 实际构造：`Mzk1G1D1LettersActual.d1AnalyticInput_of_letters` **DONE 04:16:07**，但其 `D1LetterSource` 的 `hlarge` 参数是显式义务：
  - `hC4`（v2 C4）：**条件**，owner david/kurt/sophie；等 kurt/david v2 λ 权 hstepVIII + hP5/hθ/hVIII。
  - `hSD`（tripodal S_ar）：owner david（`hcond`/`logDiff`，`Mzk1ULHcondChainActual` 00:48:16 给骨架；sophie `D4Inputs.S_ar`）。
  - `hlup`/`hlog`（D2 第二式/正性）：owner sophie（`D4Inputs.d2 : D2SecondForm`，`Mzk1ULD2SecondFormCorollariesActual` 04:18:04 给分解）；**D2SecondForm 的 λ 真实例仍条件**。
- 结论：P8 的 hOmega 输入 = **条件包条件（P8 ← D1 ← D4 ← C4/D2）**，当前未闭合。

### 1.2 DL（F7 D(L) ≤ log rad + C7）
- 接口：`Mzk1HT87F7F8F9InterfaceActual.RouteF7Statement`（NO INHABITANT）。
- 实际 `D(L) ≤ log rad + C` 需 alan §8.2/4c 的 place/different 数据；**缺失/条件**（owner alan）。
- P8 的 C7 因此是条件常数。

### 1.3 hPi（F8 高度链）

- 第一式：`Mzk1G1F8ChainActual.f8_chain_chart0` DONE 21:34:21；包装 `Mzk1G1F8BoundsActual.f8_h_pi_bound` **DONE 04:03:08**。
- 第二式（frame/ω_E）：`Mzk1G1F8O1Actual.f8_second_equality_omegaE_frame` DONE 23:09:52，消费 grace `b3_frameHeight_omegaE_eq` 22:58:40。
- `Mzk1G1F8BoundsActual.f8_h_omega_bound`/`f8_first_second_combined`/`f8_Olog2_bound` DONE 04:03:08。

### 1.3b 复核（Lead 2026-11-17 19:20）：F8 无 MISSING

- `P8AssemblyInput.perTriple` 只含**抽象实数** `hPi` 与不等式 `|hPi − n/(n−3) hOmega| ≤ C8`、
  `log c ≤ hPi + C9`；它不引用任何具体 F8 定理（F8 定理用来**生产**这些字母）。
- 生产件（均 DONE）：`F8ChainActual.f8_chain_chart0` 21:34:21、`F8PiActual.f8_pi_height_chart0` 21:00:11、
  `F8SecondActual.f8_second_equality_p1ChartHeight`/`_H0frame` 21:23:50、
  `F8O1Actual.f8_second_equality_omegaE_frame` 23:09:52（用 `b3_frameHeight_omegaE_eq` 22:58:40）、
  `F8BoundsActual.f8_h_pi_bound`/`_h_omega_bound`/`_first_second_combined`/`_Olog2_bound` 04:03:08。
- **无任何 `b3_omegaE_iso`/`omegaEIsoUnit_eq` 引用**；这两者可标可选/待消义务。
- `F1ConsumeActual` 00:38:38 提供 `f1_transport_apply`/`f1_transport_mem_H0`；F8/F1 链**不需要**
  「Čech-to-scheme height bridge」（Lead 裁定 route L838-848 走显式 Fermat 方程论证，已在 F8Local/F8Chain 实现）。
- 若未来下游需要 scheme/divisor 高度，精确缺口应是：一个未定义的 `b3SchemeHeightOmega` 及
  `|frameHeight Φ omegaYEUnit − b3SchemeHeightOmega| ≤ C`；当前 P8 组装不消费它。
- 结论：**F8 O(1) 在 frame 层已闭合**（Lead 裁定不需要 scheme Arakelov 高度）；`omegaEIsoUnit_eq`（B3 第二等式完整 unit）标**可选/待消义务**，不阻塞 F8（`coord/B3-OMEGAE-NECESSITY.md`）。

### 1.4 transport（log c ≤ hPi + C9）
- 消费 accepted `Mzk1P8HeightDictionaryActual.p8_perTriple_dictionary`（DONE）+ `abcRationalPoint_logHeight₁`（accepted）。
- F9 组装：`Mzk1P8ProducerAssemblyActual.freyJProductCriterion_of_routeF9` DONE。
- 常数 C9 由 D1/F7/F8/F9 的常数合成；当前条件。

## 2. F1–F9 / B / D / GK / A / P 清单

| 节点 | 实际件 exact 名 | 状态 | owner/义务 |
|---|---|---|---|
| F1 transport | `Mzk1G1F1HeightTransportActual.F1HeightTransportData`/`f1_frame_mem_H0`；`F1ConsumeActual.f1_transport_apply`/`_mem_H0` | DONE（接口+消费者） | 实际几何 transport 数据仍是接口（框架 DONE） |
| F2/F3 conductor | `Mzk1HT84F4F5InterfaceActual.F4Statement`/`RouteF2F3Statement` | **NO INHABITANT** | alan 8.2 conductor/different cancellation |
| F4 κ | `Mzk1HT84F4F5InterfaceActual.F4Statement`/`routeF4_of_F5Statement` | 条件 | alan/κ_i = r_i/(n−3) |
| F5 | `Mzk1HT84F4F5InterfaceActual.F5Statement` | **NO INHABITANT** | alan/§8.4 |
| F6 η | `Mzk1G1F6EtaChoiceActual.routeF6_of_F1_to_F5_choice` DONE 21:48:23；`F5F6ConsumeActual.f6_eta_choice_consumption` DONE 00:55:18 | DONE（算术） | F5 实际数据待 alan |
| F7 | `Mzk1HT87F7F8F9InterfaceActual.RouteF7Statement` | 条件 | alan §8.2/4c |
| F8 | 上表 1.3 | **DONE（frame 层）** | `omegaEIsoUnit_eq` 可选 |
| F9 | `Mzk1P8HeightDictionaryActual.p8_perTriple_dictionary` DONE；`Mzk1HT87F7F8F9InterfaceActual.routeF9_of_F6_to_F8` DONE | DONE（组装） | 输入 F6/F7/F8/transport 条件 |
| B1 | `Mzk1G1B1DependentActual.b1FiniteProducer_of_dependent` 00:45:08；`B1FinalHAvoidActual.b1FiniteProducer_of_branch` 10:39:04；`B1Chart0Actual.b1FiniteProducer_of_chart0_data` 10:51:03 | **conditional** | **O5 OPEN**：一般 T 的 `T⊆DTFixed` 选取/hbranch（grace A3 + F2.1/F2.3）；M2 解析 h（henry/kurt） |
| B2 | `Mzk1G1B2Fixed5Actual.psiFixed_preimage_p1Zero_eq_DT` 23:43:49 | **DONE** | 可与 grace `B1DTZeroFibre.psiFixed_preimage_p1Zero_eq_DTFixed_viaRR` 互校 |
| B3 | `b3_pullbackO1_iso` 23:44:37；`b3_frameHeight_omegaE_eq` 22:58:40；`frameHeight_congr` 23:34:27 | DONE（frame 层）；`b3_omegaE_iso`/`omegaEIsoUnit_eq` **可选/待消义务**；全仓 grep 确认无 Lean 证明引用（仅 docstring） | grace |
| D1 | `Mzk1G1D1ProducerActual.d1_of_analyticInput` 21:11:19；`Mzk1G1JHeightUniformActual.jHeight_relation_deg` 19:41:14；`height_dictionary_deg` | DONE（conditional on D1AnalyticInput） | 见 1.1 |
| D2 | `Mzk1ULD2SecondFormActual.D2SecondForm`；`Mzk1ULD2SecondFormCorollariesActual` 04:18:04 | 接口/λ 实例条件 | sophie |
| D3 | `Mzk1G1JHeightUniformActual`（D3 per-K + uniform） | **DONE** | — |
| D4 | `Mzk1G1D4BridgeActual.d4_absorption`/`d4_of_c4_qscale` 00:43:15；`d4_of_c4_qscale_legacy` INTERIM | **DONE（纯实数）** | `hC4_v2` 等 letters 是显式输入；`uc_c4_actual_paper_letters` 21:25:34 |
| D4Inputs | `Mzk1ULD4InputsActual.D4Inputs` 00:46:08（Q_eq/M_eq/S_ar_eq/hlogK/hsQ/d2） | DONE（结构） | hlogK/hsQ λ 版待 david；hC4 待 kurt/david |
| G-K | `Mzk1G1DisjointFamilyActual.hasGluedBelyiFamily_of_b1`；`Mzk1G1UniversalLocalFieldExistsFinalActual.universalLocalFieldExists_final` 00:05:48 | 条件 | b1FiniteProducer（O5 OPEN）+ `ResidueRootGeneration`（alan）+ K_V/δ0 紧性（kurt `L_p`/grace `IsProper`） |
| A4/A5 | `a5_lineBundle_iso`（grace 19:19:24）；`Mzk1G1Omega*` | A5 DONE；A4 接口 | grace/henry |
| P5/hP5 | `Mzk1ULHpktActual.Hpkt`/`paperA`/`paperEar`/`hprime_paperConstants`（UCHpkt:191）；`Mzk1UHprimeActual.hprime_paperLstarLogs_le` 00:28:56 | hprime DONE；hP5/J1-M 条件 | kurt J1-M §8 |
| P6 constants | `Mzk1P6HConstActual` | DONE | — |

## 3. D1–D4 与 P5 接线（条件包条件传染点）

1. **P8 ← D1 ← D4 ← C4**：`P8AssemblyInput.perTriple` 的 hOmega 界来自 `D1AnalyticInput.upper_estimate`；`D1Letters.hlarge` 的 `hC4` 来自 v2 C4；v2 C4 又依赖 hstepVIII（kurt λ 权）+ hP5/htheta/hstepVIII。⇒ 当前是三层条件嵌套，**不是单层条件**；只有在 kurt/david 的 v2 hstepVIII 真证 + david letters 实例化后，`D1LetterSource` 才能消参，D1AnalyticInput 才无条件。
2. **D1Letters.hSD/hlup/hlog ← D4Inputs/D2**：`D4Inputs` 的 `hlogK`/`hsQ` 是**显式义务**（david λ 版真证未到），`d2 : D2SecondForm` 是结构接口；⇒ 不能把 `D4Inputs` 当作已闭合输入。
3. **P8 ← G-K ← B1（O5 OPEN）**：`P8AssemblyInput.perTriple` 的 uniform `n/δ` 与固定 φ_i/K_V 来自 G-K；G-K 的 `hasGluedBelyiFamily_of_b1` 需要 `b1FiniteProducer`，而 B1 只在 chart-0 有理 T 的 restricted class（`B1Chart0`）与 `hbranch` 条件（`B1FinalHAvoid`）下给出；**一般 T 的 O5 未闭合**。⇒ P8 的 uniform 常数不能宣称无条件。
4. **P8 ← F6 ← F5**：F6 的算术（eta choice）DONE，但 F5 是 NO INHABITANT（alan）；⇒ `perTriple` 的 C6 仍条件。
5. **P8 ← F7**：F7 是 NO INHABITANT（alan）；⇒ C7 条件。
6. **P8 ← F8**：frame 层 DONE；若下游要 scheme/divisor 高度，`omegaEIsoUnit_eq` 是可选义务，不影响当前 F8 链。
7. **P5/hP5**：`hprime` DONE（UCHpkt 复用），但 `hP5`/J1-M（`-M_paper_v2 ≤ θ_λ`）仍条件（kurt）⇒ C4 的 `Q/M` 实际实例仍条件。

## 4. 结论

- P8 组装骨架与 F8/F9/B2/D3/D4 纯实数部分已 DONE；**P8UniformHeightBound 仍未无条件可达**，因为 `perTriple` 依赖 D1（C4/D2）、F5/F7、G-K（B1 O5）三组条件输入。
- 隐藏缺口（审计暴露）：
  1. **D1 条件包条件**（hC4 ← hstepVIII ← hP5/htheta/VIII）——最容易在汇报中误记为「D4 已闭合」；
  2. **D4Inputs.hlogK/hsQ 是显式义务**，不是已证 λ 版；
  3. **G-K 的 B1 只在 restricted class**，一般 T O5 OPEN；
  4. **F5/F7 无 inhabitant**（alan），P8 的 C6/C7 全是条件常数；
  5. **P5/hP5/J1-M 条件**，C4 Q/M 实例未消参。
- 本审计不计任何节点闭合；建议在全链收口前按上述五组逐项消参，并保持 P8 输出的 docstring 标 conditional。
## 5. ψ 在 `t^n=1` 的 `(t,0)` 点分歧：对 B1/P8 口径的影响（2026-11-17 20:15）

grace 发现：`psiFixed` 的 chart-0 零纤维在 `t^n = 1` 的 `(t,0)` 点有 n 阶零（`dx = 0`），
故 ψ 在该点分歧；route B2 的「0 纤维无分歧」对具体 `psiFixed` 只在
`T ∩ {t : t^n = 1} = ∅` 时成立（general T 需 A3 RR 的 reduced s0）。

**本 lane 的代码消费核对（grep/证明体检查）**：
- `Mzk1G1B1FinalHAvoid.b1FiniteProducer_of_branch`：只消费 `B1DependentActual.b1FiniteProducer_of_dependent`，
  即 **boundary 预像有限 + `AvoidsBoundary n (phiFixedL n Tr h hh) T`**；**不消费** `0 ∉ Branch(ψ)` 或任何无分歧/导数条件。
- `Mzk1G1B1Chart0Actual.b1FiniteProducer_of_chart0_data`：只消费 `hdata`（chart-0 有理坐标证书）
  + emmy `phiFixedL_T_avoid_data`（hT + h0）+ dependent 接口；**不消费** ψ 无分歧。
- `Mzk1G1B1HAvoidFinalActual`：只做素理想含 `h(u)`/`h(u)-1` 的判定；**不消费** Branch/Ram。
- `Mzk1G1B2Fixed5Actual` / `B1Chart0` 的 B2 全局零纤维：`psiFixed_preimage_p1Zero_eq_DT` 是**点集等式**，
  不声明 ψ 在 0 纤维无分歧；分歧点不影响该等式。
- P8 `perTriple.hPi` 只含抽象高度/误差；F8 四引理（`f8_*`）不引用 Branch/Ram；
  **P8 组装当前不消费 `0∉Branch(ψ)`**。

**Lead 裁（2026-11-17 20:35）**：grace 的条件版 F2.2（`hT : ∀t∈T, t^n≠1`）**不是 route B2 的达成**，
只是 **restricted diagnostic only**；route B2 的一般形式依赖 A3 RR 的 ψ（u0/u1 from H⁰(O(D_T))，reduced s0），
因此 F2.2 条件版**不计闭合**、也**不计入 B2 状态**。由于 B1/P8 当前不消费 `0∉Branch(ψ)`（见下），
F2.2 目前**不是阻塞项**；只在未来需要 `0∉S1` 时作为显式附加条件登记。
**结论**：B1 的 restricted-class 声明（`B1Chart0`）与 conditional 主链（`B1FinalHAvoid`）**不受该事实影响**；
它们从不消费「ψ 在 0 无分歧」。该事实只影响 route B2 的**无分歧语义附加结论**（不在 B1FiniteProducer 的需求内）。

**若未来 P8/G-K 的 `S1 = ψ(S) ∪ Branch(ψ)` 需要 `0 ∉ S1`（例如 h 的选取避 0），**
必须作为 `hbranch`/T 选取的**显式附加条件**登记：`0 ∉ Branch (psiFixed n Tr)` 或
`T∩{t:t^n=1}=∅`；当前 G-K `phiFixedL_T_avoid_data` 只要求 `T⊆DTFixed` + `h.eval 0∉{0,1}`，
**不要求** `0∉Branch(ψ)`；若后续 block 需要，按 O5 之外的新附加义务记录，不伪装为已消。
## 6. `D1Letters.hlarge` 的 `hC4` 与 david C4 letters 接法核对（2026-11-17 20:20）

### 6.1 C4 letters 的实际形状
`Mzk1UCC4PaperActual.uc_c4_actual_paper_letters`（DONE 21:25:34，参数化 Q/M/hP5/htheta/hstepVIII）的结论：
```
cL (l.value) * Q ≤ paperA (dMod T) (l.value) (SAr_tripodal T) (paperEar (eMod T) (l.value) etaPrm)
```
其中 `cL l = 1/6 - 2/l^2`、`paperA d l S E = (1 + 12 d/l) S + 10 E`、
`paperEar e l eta = eStarMod e * l + eta`（`eStarMod eMod = 2^12·3^3·5·eMod`）。
它是 **全局 IUT 数据 `T : SourceNativeInitialThetaData l`（l=prime≥5）层面**的字母，
`Q,M` 是传入的实数（paper Q=v2、M=Mpaper_v2），`S_ar=dMod T`、`eMod=eMod T` 均为全局。

### 6.2 `D1LetterSource.hlarge` 需要的形状
```
(1/6 - 2/l^2) * jHeight lam
  ≤ (1 + 12*dmod/l) * S + 10*(emod*l + eta)
```
且 `S ≤ discOver K + truncConductor lam`（per-(K,λ)），`hlogK/hsQ` 提供 `hlup/hlog`。

### 6.3 直接对接的障碍（重要）
1. **全局 vs per-λ**：C4 的 `Q` 是全局 q-pilot 量（同一 IUT 数据固定），而 `D1Letters.hlarge` 的 Q 是 **per-λ `jHeight lam`**。
   若按 Lead 裁决「C4 的 Q = D4 的 h = jHeight」，则必须对**每个 λ** 实例化 C4（`Q := jHeight lam`），
   即需要 kurt 的 **per-λ hP5/htheta/hstepVIII**（`-M ≤ θ_λ`、`θ_λ ≤ Hpkt`、hstepVIII 中的 `-cL Q` 项按 Q=jHeight lam）。
   现有 `uc_c4_actual_paper_letters` 只给 global Q 一次，不能直接用于所有 λ。
2. **S 的选取（david 2026-11-17 20:23 更正）**：per-λ C4 应取 `S := discOver K + truncConductor lam`（**不是**全局 `SAr_tripodal T`），于是 `hlarge.hSD` 直接 `le_rfl`，**不需要** per-λ `SAr_tripodal ≤ discOver+truncConductor` 上界；剩余真义务是 `log d_Ftpd = discOver K`（logDiff_eq）与 `log f_Ftpd ≤ truncConductor lam`（hcond），由 Legendre 相等 + conductor 逐位给出。
3. **e* = eStarMod(eMod T)**：`hlarge` 的 `emod` 应填 `eStarMod (eMod T)`（不是 `eMod T`）；`eta` 填 etaPrm。
4. **l 的选择**：C4 的 `l = l.value`（固定 prime≥5），而 D4/D2 的 `l` 由 Cor 2.2 逐 λ 选择（`√h≤l≤C_d√h log(2C_d h)`）；
   需证明可令 `l.value` 满足 D2 第二式，或引入 l 的替换（需 david/kurt 确认）。

### 6.4 消参补丁计划（按 david 2026-11-17 20:28 确认）

per-λ C4 实例应采用：
- `Q := jHeight lam`（D4 的 h=Q_all）；
- `S := discOver K + truncConductor lam`（**不是**全局 `SAr_tripodal T`）；于是 `hlarge.hSD` 取 `le_rfl`；
- `dmod := dMod T`（或 per-λ 对应），`emod := eStarMod (eMod T)`，`eta := etaPrm`；
- `l` 由该 λ 的 exclusion set 按 D2 第二式选出（`√h ≤ l ≤ C_d√h log(2C_d h)`），**不能沿用固定 l.value**；
- 每 λ 独立实例化 C4 的 hP5/htheta/hstepVIII（kurt per-λ C4；M := jHeight λ/(2l)）。

补丁顺序（david 给出）：sophie `LegendreTripodalEq`（域=Q(λ)）→ david `hcond` per-λ + hlogK/hsQ λ 数值界 → kurt per-λ C4 → andrew 填 `hlarge`。
当前 `D1AnalyticInput` **不能消参**（`hlogK/hsQ λ` 与 per-λ C4 仍是显式义务）。

- 若 kurt 提供 per-λ C4 实例（`Q := jHeight lam` 的 hP5/htheta/hstepVIII），则：
  `hC4 := (uc_c4_actual_paper_letters … Q:=jHeight lam …)` 经 `cL`/`paperA`/`paperEar` 定义展开；
  `S := SAr_tripodal T`，`dmod := dMod T`，`emod := eStarMod (eMod T)`，`eta := etaPrm`；
  `hSD := tripodal 逐 λ 上界`（david `hcond`/`logDiff` λ 版）；`hlup/hlog` 由 D2 第二式（sophie `D2SecondForm`）。
- 当前 hP5/htheta/hstepVIII 仍是全局义务；`hlogK/hsQ` λ 真证（david）仍是显式义务 ⇒ **`D1AnalyticInput` 尚不能消参**。

## 7. P8 perTriple 可提前接线的无条件件（说明，不新增 Lean）
- `perTriple` 需要（hOmega, DL, hPi）与四个界同时给出；单独的无条件件**不能**直接构造 `P8AssemblyInput`（缺 hOmega/DL）。
- 已无条件可用的组件（作为函数/证明供组装）：
  - `hPi`：`F8ChainActual.f8_chain_chart0`、`F8PiActual.f8_pi_height_chart0`、`F8SecondActual.f8_second_equality_*`、`F8O1Actual.f8_second_equality_omegaE_frame`、`F8BoundsActual.f8_*`（DONE）；
  - transport：`Mzk1P8HeightDictionaryActual.p8_perTriple_dictionary` + `abcRationalPoint_logHeight₁`（DONE）；
  - B2 点集：`Mzk1G1B2Fixed5Actual.psiFixed_preimage_p1Zero_eq_DT`（DONE，供 b2 语义用）；
  - D3：`Mzk1G1JHeightUniformActual`（DONE）；
  - D4 纯实数：`Mzk1G1D4BridgeActual.d4_absorption`/`d4_of_c4_qscale`（DONE）；
  - F9 组装：`Mzk1HT87F7F8F9InterfaceActual.routeF9_of_F6_to_F8` / `freyJProductCriterion_of_routeF9`（DONE）。
- 接线说明：这些件可在 `P8AssemblyInput.perTriple` 的构造中作为局部证明使用，但 **hOmega（D1）与 DL（F7）未无条件化前，perTriple 仍条件**；不建议在汇报中把局部接线当作 P8 输入闭合。