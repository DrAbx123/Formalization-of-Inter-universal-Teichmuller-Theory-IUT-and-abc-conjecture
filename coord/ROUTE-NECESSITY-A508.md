# ROUTE NECESSITY — 3.12 vs ABC/height：hcomp 两条 gap 与 θ-hull 比较（A508）

日期: 2026-11-11。只读审计；不写实现。引文行号均取自本仓 corpus:
- `papers/motizuki_corpus/text/Formalization of IUT (2026-04).txt`（下称 **Form**）
- `papers/motizuki_corpus/text/Inter-universal Teichmuller Theory III.txt`（**IUT III**）
- `papers/motizuki_corpus/text/Inter-universal Teichmuller Theory IV.txt`（**IUT IV**）

## 0. 结论先行

1. **hcomp 两条 gap（我们 Lean 的 `Cor312EpsilonArithmeticComparison` 两个字段）不是 3.12 的必要前提，而是 ABC/height 阶段（Stage 5: IUT IV/ExpEst）的输入。** 它们是把 Cor 3.12 的 `CΘ ≥ −1` 转成 ABC 高度不等式时的算术线丛/高度比较与 log-volume 估计。
2. **θ-hull 侧要分两种读法**：
   - **(a) Θ-pilot hull log-volume 及其与 q-pilot log-volume 的比较**（`R≤−|log(Θ)|`、`−|log(q)|∈R`）——**这是 3.12 的内容本身，3.12 必需**（IUT III 10843-10898；Form §4 619-621）。hull+det 被移到 3.11.5，因此 **hull 的计算是 3.12 路线必需**（Form 578-580, 611-618）。
   - **(b) 我们 ABC-bridge 里把 hull log-volume 当作 θ-pilot 上界加进 region log-volume 估计（hcomp gap2 的 `(logVolume hull).toReal`）**——**ABC 必需，3.12 不需要**。
3. 因此用户假设**部分成立**：hcomp 两条确实可以移出"3.12 必需"清单；但"θ-hull 比较"若指 q/Θ-pilot 的 log-volume 比较（3.12 的结论），则**不能**移出；只有 hull bound 在 ABC 估计中的用法可以移出。
4. 当前登记（`FOUNDATION-COVERAGE.md:36,44,56`）把 hcomp 混在 O12（Cor 3.12）里，建议拆成 **O12a（3.12：q/Θ-pilot hull log-volume 比较，必需）** 与 **O12b（ABC：hcomp 两条 IUT IV 比较，ABC-only）**。

## 1. 论文形式化路线（逐条 + 行号）

| 论文步骤 | 行号 | 需要的对象/输入 | 我们 Lean 对应 | 登记为 named gap？ | 必要性 |
|---|---|---|---|---|---|
| Stage 1 = [IUTchIII] Thm 3.11 ⇒ Cor 3.12 | Form 114-118 | Thm 3.11（(dsc)+APT+IPL 部分）+ 3.11.5（hull+det+SHE+IPL）+ q/Θ-pilot 比较 | `Mzk1FourTriangleSharedActual`、`StepProviderPrime/StepProvider'`、O12 相关 | 部分（O12 为 named same-C） | **3.12 必需**（本身就是 3.12） |
| Stage 2 = Thm 3.11 modulo [IUTchI-II] | Form 118-120 | multiradial algorithm、Ind1/2/3、Hodge theater、log-shell/tensor packets | `MultiradialAlgorithm.lean`（Obligation）、Ind1/2/3 Reduction、C3 tensor packets | 是（大量接口/named） | **3.12 路线必需**（3.11 的前提） |
| Stage 5 = numerical aspects（[IUTchIV], [ExpEst]） | Form 121-124 | IUT IV 显式 log-volume 估计、C_Θ 估计、ABC 高度比较 | `Cor312ToABCBridgeInterface` 的 hcomp 两条；`ThetaBoundToHeightWeight` | 是（hcomp = 显式 named gap） | **ABC 必需；3.12 不需要** |
| 四三角：第 1/2/3 个 △ | Form 443-547（图 472-501；解释 503-546） | BPS → multiradial rep（Ind1/2/3）；dsc 下降；HDD=(hull+det)∘(dsc) | `FourTriangleSynthesis`、`HDDDecomp/HDD`（接口） | 部分 | **3.12 路线必需** |
| 四三角：第 4 个 △ = (HDD)∘(SHE) | Form 536-547 | 同一 ring/common container 下 **Θ-pilot（HDD）与 q-pilot（SHE）的同时比较** | O12 q/Θ-pilot hull log-volume 比较（`qThetaPilotLogVolumeComparison`） | 是（O12 named） | **3.12 必需**（第 4 三角 = Cor 3.12 的核心内容） |
| "3.11.5 ⇒ 3.12" 重组：把 hull+det 从 3.12 移到 3.11.5 | Form 568-580 | hull+det（holomorphic hull、det/log-volume）、SHE、IPL | `thetaPilotHullLogVolumeReal`、`packetLogVolume/matrixLogDet`、SHE 文件、IPL | 部分 | **3.12 路线必需**（hull+det 是 3.11.5 的组成部分） |
| APT 在 1st/2nd/3rd △ 的作用 | Form 581-601 | 算法平行移动（APT）、IPL | （接口/named） | 是（缺） | **3.12 路线必需** |
| 三个箭头形式的总结图 | Form 602-621 | Thm 3.11: (dsc)+APT+IPL ⇒ 1st/2nd/3rd；Thm 3.11.5: (hull+det)∘(dsc)+SHE+IPL ⇒ 4th；Cor 3.12: comparison of q-,Θ-plts | 同上 | — | 总结性证据 |
| IUT III Cor 3.12 证明 Step (xi)：构造 determinant of arithmetic line bundles + normalized log-volume of regions → `R≤−|log(Θ)|`；`−|log(q)|∈R` | IUT III 10835-10852（10843-10848 定义 R 与 −|log q|） | 算术线丛 determinant、log-volume 归一化、region 1,◦U / q-pilot region | `S3137` hull/volume 律、det 簿记（`matrixLogDet`/packetLogVolume） | 部分 | **3.12 必需** |
| (xi-d/e) log-Kummer 校正 vertical shift；multiradial algorithm + **holomorphic hull** + log-volume 产生 `R≤−|log(Θ)|`；IPL/SHE 连接到 `−|log(q)|` | IUT III 10853-10887 | log-Kummer 对应、holomorphic hull、IPL、SHE | `logThetaLattice`（接口/壳）、hull 资产、SHE | 部分 | **3.12 必需** |
| (xi-f) 形式结论：`−|log(q)| ∈ R≤−|log(Θ)|`，故 `−|log(q)| ≤ −|log(Θ)|`，即 `CΘ ≥ −1` | IUT III 10888-10898 | 上述 inclusion | `qThetaPilotLogVolumeComparison`（obligation） | 是（O12 named） | **3.12 必需（=3.12 的结论）** |
| (xi-g) summary：两种 tautologically equivalent 计算 q-pilot log-volume 的方式 | IUT III 10899-10903 | 上述全部 | — | — | 3.12 内容 |
| ABC 主定理（Theorem A：canonical height 不等式） | IUT IV 106 | **height**（canonical height）与 Θ-pilot log-volume 估计 | `Cor312ToABCBridgeInterface` 的 hcomp 两条 | 是（hcomp） | **ABC 必需；3.12 不需要** |
| 显式估计：用 Cor 3.12 的 `CΘ ≥ −1`、估计 CΘ | IUT IV 394-395, 1257-1376, 1583-1585 | IUT IV §2 算术线丛/高度比较 + ExpEst 数值估计 | hcomp 两条 + `ThetaBoundToHeightWeight` | 是 | **ABC 必需；3.12 不需要** |

## 2. 我们 Lean 中的精确对象

| Lean 声明 | 文件:行 | 语义 | 论文对应 | 必要性判定 |
|---|---|---|---|---|
| `Cor312EpsilonArithmeticComparison` | `LeanFormal/IUT/ABCBridge/Bridge/Cor312ToABCBridgeInterface.lean:224` | per-ε ABC 高度比较数据（`logShellPoint` 数据 + 两个 gap 字段） | IUT IV §2（Stage 5） | **ABC 必需；不是 3.12 前提** |
| `height_le_normalizedRegionVolume`（hcomp gap 1） | 同上 :236 | `logHeight₁ ≤ (1+ε)·region log-volume` | IUT IV §2 算术线丛/高度比较 | **ABC 必需；3.12 不需要** |
| `regionVolume_le_normalizedWeight`（hcomp gap 2） | 同上 :248 | `region log-volume ≤ (1+ε)·arithmeticWeight + hull log-volume + D` | IUT IV §2 log-volume 估计 | **ABC 必需；3.12 不需要**（其中 hull log-volume 作为加法常数属于 ABC 用法） |
| `qThetaPilotLogVolumeComparison` / `_iff` | `S3137QThetaPilotLogVolumeReadingsActual.lean:145/149`；`S3137ThetaHullVolumeScalingActual.lean:79` | q-pilot reading 与 Θ-hull log-volume 的比较 obligation | IUT III 10843-10898（R≤−|log Θ|、−|log q| 的 inclusion） | **3.12 必需（这是 3.12 的内容）** |
| `thetaPilotHullLogVolumeReal`（= log Haar(actual region)） | `S3137ThetaHullVolumeScalingActual.lean:70` / `AbsTopIII09:62` | Θ-pilot hull log-volume | IUT III 10846-10848, 10880-10882（holomorphic hull + log-volume） | **3.12 路线必需**（hull+det 在 3.11.5） |
| `IQHullLogVolumeInterface.hull_logVolume_lt_top` | `Corollary312/StepXI/HolomorphicHull/SourceHullCompactnessReduction.lean` | hull finiteness | IUT III 3.12 的 finiteness（−|log Θ|∈R） | **3.12 必需（finiteness）**；其作为 ABC gap2 的加法常数用法是 ABC-only |
| `thetaPilotLogImage := qPilotLogImage/(2*l.value)` | `Mzk1QPilotR4Stage5AlignActual.lean`（A497 判 VOID） | 空转 θ 读数 | 无 | **都不需要（VOID，不得用）** |

## 3. 对用户假设的回答

- **"hcomp 两条 gap 可能不是 3.12 的必要前提"**：成立。它们是 IUT IV §2/Stage 5 的输入，用于把 Cor 3.12 的 `CΘ ≥ −1` 变成 ABC 高度界；3.12 的证明（IUT III Step (xi)）不需要它们。
- **"θ-hull 比较可能不是 3.12 的必要前提"**：**部分成立、需拆读法**：
  - 若指"q/Θ-pilot 的 hull log-volume 比较"（`R≤−|log(Θ)|` vs `−|log(q)|`）——**是 3.12 必需**，这就是 3.12 的结论（IUT III 10895-10898；Form 619-621）。
  - 若指"我们 ABC-bridge 中把 hull log-volume 当作 θ-pilot 上界/加法常数"（hcomp gap2 的 hull 用法）——**ABC 必需、3.12 不需要**。
  - 若指"θ-pilot hull log-volume 的**有限性/数值计算**"——3.12 的 finiteness 断言与 3.11.5 的 hull+det 需要（IUT III 10846-10852, 10880-10886；Form 578-580），不能移出。
- **建议调整登记**：把 `FOUNDATION-COVERAGE.md:36/44/56` 的 O12 拆为
  - **O12a（3.12 必需）**：q/Θ-pilot hull log-volume 比较（`qThetaPilotLogVolumeComparison`）+ Θ-pilot hull finiteness；
  - **O12b（ABC/Stage 5 必需，3.12 不必需）**：hcomp 两条 IUT IV 比较（`Cor312EpsilonArithmeticComparison` 两字段）。
  这样登记与论文路线一致，也避免用 ABC 阶段 gap 阻塞 3.12 的"对象先行"。

## 4. 副作用检查

- `Cor312ToABCBridgeInterface` 声明其 `hcomp` 两条是"exactly the two still-unproved paper links"（文件 63-73、91-100 行）：这是对 **ABC bridge** 成立的表述，不应被读作 3.12 的必需前提。
- 3.12 一侧（`qThetaPilotLogVolumeComparison`）是 named same-C obligation，不是 hcomp；两者在 `OBJECT-STATUS-A499.md:26` 中同列 O12，建议按上面拆分。
- 本审计不改变任何 Lean 文件；f4b 链继续优先。

## 7. A508 DAG 执行（lattice 审计核对）

**核对**: 独立复查了 §1–§3 的原文行号与判定，结论一致：
- 3.12 路线 = Thm 3.11（dsc+APT+IPL）+ Thm 3.11.5（(hull+det)∘(dsc)+SHE+IPL）+ q/Θ comparison（Formalization L602-621；4th △ L549-580）。
- hcomp 两字段是 IUT IV §2 内容（`Cor312ToABCBridgeInterface.lean` L67-73/L224-248），属 Stage 5（Formalization L124-125）；IUT III Cor 3.12 proof（L10354-11210）无 IUT IV 引用 → **hcomp 不是 3.12 前提**。
- Θ-pilot hull 无“独立 comparison 假设”：comparison 即 Cor 3.12 本身（Step (xi-f) L10888-10898 形式得到）；`independent-theta-pilot-readout` 是 OBJECT 需求（-|log Θ| 的定义）；`literal-hull-finiteness` 是 3.12 的有限性断言（L10351/L10408-10411）。
- `contract-provenance` 是我们 StepXIContract 自身 artifact（`Contract.lean:32-44` 允许 target:=theta），不是 paper 步骤；应重做/绕过 contract。

**DAG-BLOCKED 更新（已执行）**:
- 加 `route_necessity` 字段（20 条）；新增 `named-gap:literal-hull-finiteness`（3.12）与 `named-gap:contract-provenance`（neither/artifact）；blocked_total=90。
- `meta.a508_3_12_critical_path` = [independent-theta-pilot-readout, literal-hull-finiteness, takkun-containment, gate:objects-not-constructed]。
- `meta.a508_abc_chain_gaps` = [hcomp-iut4-comparisons, request-P-received-hull, takkun-hull-bound, abcbridge:Cor312EpsilonArithmeticComparison.twoNamedGaps]。
- `meta.a508_neither` = [contract-provenance, external-lana-reference, vacuity:qTheta-chain, shell:*, interface:hdddecomp-fourtriangle]。
- 已改正 hcomp entry 的旧措辞（不再写“Cor312 链真正内容”而写“ABC/height 阶段唯一真内容，不是 3.12 前提”）。
- 保留 ABC 链登记（不删除历史）；3.12 关键路径现在只含 paper 路线对象/有限性/Takkun 桥与对象 gate。

