# C0 — N8 target signature: SHEAF stage-1 record

任务 ID / 所属组 / owner / 日期：C0 / N8 closure / qside / 2026-10-22
目标节点 / SHEAF 阶段：C0 TargetSignature / stage 1 (statement/scope), no Lean finalization.
文件：write `tmp/sheaf/n8/closure/C0-STAGE1.md` (this file).  Future Lean file `tmp/sheaf/n8/closure/TargetSignature.lean` is NOT to be finalized before stage-1 review.  The earlier trial `TargetSignature.lean` is a discarded candidate and is not used by any consumer.
集成负责人 / 构建负责人：C0 owner; C10/N8Assembly integrator later.
共享接口与冲突：C0 freezes only source/input/output roles; C1–C9 must use the same `OriginalInput` index.  C0 must not change `OriginalInput`, `SourceTheorem311Realization`, `SourceDefinition31Data`, `SourceHodgeTheaterFamily`, `StepXIContract`, or `SourceImageHull` semantics.
续领范围：after review, C0 Lean signature; C1 SourceInputBinding; C3 SourcePilotRegion.

## 1. 数学目标（完整对象、量词、假设、结论）

C0 不是“定义一个签名就完成”。它冻结整条 N8 链的总目标角色：

```text
对每一份原文允许的源输入
  l : PrimeGeFive,
  V : Type uv,
  I : OriginalInput.{u, uv, upi, umon, ui} l V,
构造一个输出包 O，其中包含：
  (1) 实际源 Theorem 3.11 数据 (a)(b)(c)，带 Ind1/Ind2/Ind3 的实际作用/包含方向和函子性/跨列结论；
  (2) 同一构造的实际 IPL/SHE/APT 算法相容（不是自由字段）；
  (3) 实际区域的 holomorphic hull U 与同一原文归一化 log-volume；
  (4) 实际 q-pilot 值 Q(I) 与实际 theta hull 值 Θ(I)，Θ(I) 有限，且 Q(I) ≤ Θ(I)；
  (5) 实际 arithmetic degree / determinant / 权重对应关系。
```

量词和输入边界：`l,V,I` 是原文允许输入；`v : V`、实际 source image realization、`n : ThetaPilotCarrier l`、`j : SignedLabel l.value` 属于链内 C1/C3 必须产生/固定的源数据，不作为 C0 的自由输入。C0 输出必须包含它们或由它们定义的量。

## 2. 原文位置

- IUT III, Theorem 3.11 及 proof 的 (i)(ii)(iii)，Corollary 3.12，Steps (xi-a)–(xi-g)，IPL/SHE/APT 段落：papers/motizuki_corpus/text/Inter-universal Teichmuller Theory III.txt，重点 9676–9794，10324–10352，10823–10898。
- Ob3 / determinant / arithmetic degree：IUT III 7932–7987；IUT IV 671–682（局部归一化）和 1009–1054（权重转换）。
- 原文输入：IUT III Theorem 3.11 开始处的 initial Theta-data 与 `{n,m HT}` Hodge theaters；不是 packet profile、procession、vertical Kummer、evaluation 或 completed output。

## 3. 允许输入 vs 链内必须产生

### 3.1 允许输入（来自原文）

1. `l : PrimeGeFive`。
2. `V : Type uv`（地方索引型）。
3. `I : OriginalInput.{u, uv, upi, umon, ui} l V`，其真实字段为：
   - `I.initial : SourceDefinition31Data.{u} l`；
   - `I.family : SourceHodgeTheaterFamily.{u, uv, upi, umon, ui} l V`，包含索引、Hodge theater 族、distinct、link/refl/symm/trans、permutation/自然性；
   - `I.index_equiv : I.family.index ≃ Int × Int`；
   - `I.arithmetic_alignment`。
4. `SourceDefinition31Data` 已包含的 arithmetic/selectedPlaces/badPlaces/reduction/torsion/orbicurve/sections/cusp 及五组 compatibility 字段。
5. `SourceHodgeTheaterFamily` 已包含的 Hodge theater/lattice/link 数据（这是原文给定 theater/lattice）；C0 不再从任意弱数据制造它们。

### 3.2 链内必须产生的对象/性质（不能放进输入）

1. 实际 `SourceTheorem311Realization`（procession、packet、vertical、evaluation、genericFamily、labelledCount）以及 Theorem 3.11 的 (a)(b)(c) 结论。
2. 实际 log/K1/K2 连接：`SourceLogShellDatum` 的实际 log、核/像与 K1/K2 边界；`descends_iff` 只是通用下降供体，不是 K1/K2 源实现。
3. 实际 q/theta-pilot、Kummer 类、整数格/张量区域，以及改根相容。
4. 实际受约束选择 `C(I,n,x)`、求值 `eval`、可能像 `U(I,n,x) = {y | ∃ c, eval c = y}`；不得用自由 `possibleImage`。
5. 实际 IPL/SHE/APT 算法相容（Remark 3.10.2 的 Kummer 竖箭头与 evaluation 复合优先）；不得接受自由 `ipl/she/apt`。
6. 实际 λO-hull、共同控制、正有限体积；不得用“对所有缩放封闭的子幺半群”代替。
7. 实际相对 determinant、tensor 幂、全局 arithmetic degree/log-volume 对应（Ob3-3）；不得用任意 `logVolume`/`tensorPower` 字段。
8. 实际 q 输出/逼近或直接 `Q(I) ∈ Values(I)`，从而消去旧 `hq`；不得把 `Q(I) ≤ Θ(I)` 作为输入或把 `Set.Iic Θ(I)` 定义为 Values。

## 4. 实际消费者 C10

C10 是计划中的 `tmp/sheaf/n8/closure/N8Assembly.lean`（尚无文件），唯一消费者是 Corollary 3.12 / `Cor312ToABCBridgeInterface` 的实际 signed log-volume 接口；下游 ABC epsilon 高度比较是另一个下游任务。

C0 只冻结 C10 必须消费的角色。C10 必须：
- 调用 C1–C9 的实际结果；
- 不向调用者索要结论型字段；
- 不传入自由 `qSigned/ipl/she/apt/q_le_target/target_le_theta`；
- 输出实际源 3.11 数据、IPL/SHE/APT、hull/有限性、degree 和 `Q(I) ≤ Θ(I)`。

现有 `StepXIContract` (LeanFormal/IUT/IUTIII/Corollary312/StepXI/Contract.lean:32) 有自由 `ipl/she/apt : Prop` 和自由 `qSigned/thetaSigned/targetSigned`；它只能作为 C10 的下游 **consumer type**，不能作为 C0 输入，也不能当作 C0 输出已构造的证据。

## 4.1 输出字段审计表（必须逐项满足，stage2 不得写 `Nonempty` 总包）

| C0 输出字段 | 现有真实 Lean 类型 / 明确无类型 | paper anchor | consumer |
|---|---|---|---|
| 实际源 3.11 realization | `SourceTheorem311Realization.{u,v,w} l Label Choice`（SourceHodgeTheaterBridge.lean:910）；另有 `SourceTheorem311Completion`（SourceRealizationLifting.lean:43）为 source package | IUT III Thm 3.11, Def 3.1 | C10 |
| IPL/SHE/APT | **无类型/obligation**；`StepXIContract` 的 `ipl/she/apt : Prop` 是自由字段，不得算作 C0 输出 | IUT III 9676–9794; Cor 3.12 Steps (xi-a)–(xi-g) | C5, C10 |
| holomorphic hull / 有限正体积 | 真实 donor 数据：`I.sourceHolomorphicHull v R n`, `I.sourceHullVolume v R n`（SourceImageHull.lean）；无统一 hull 输出结构 | IUT III Cor 3.12; Ob3 | C7, C8, C10 |
| q/theta 值 | 真实 donor：`I.sourceThetaPilotPoint v R n j`, `I.sourceLocalLogDegree v ...`, `I.sourceHullVolume`；**无单一 signed q/theta 输出类型** | IUT III 10823–10898 | C9, C10 |
| arithmetic degree / determinant / Ob3-3 | **无类型/obligation**；`DetTensorPowerLogVolumeBookkeeping` 是自由 bookkeeping，不算输出 | IUT III 7932–7987; IUT IV 1009–1054 | C8, C10 |
| Values/q 输出/逼近 | **无类型/obligation**；不得以 `Set.Iic Θ(I)` 或自由 `possibleImage` 代替 | IUT III (xi-d)–(xi-f) | C9, C10 |
| 实际 source completion | `SourceTheorem311Completion.{u,v,w} l Label Choice`（SourceRealizationLifting.lean:43） | IUT III Def 3.1 / Ex 3.6 | C1/C10 |

C0 stage2 约束：在 C1/C3/C4/C5/C8 的精确类型未冻结前，不得把上表整体写成一个 `Nonempty N8TargetOutput` 或 `N8TargetSpec` 总包；每个字段必须先有独立真实类型/obligation、来源和 consumer，且不得用 `StepXIContract` 的自由 `ipl/she/apt`、`Output.possibleImage`、`DetTensorPowerLogVolumeBookkeeping.logVolume` 或任意 `Nonempty` 代替。

## 5. statement_dependencies（准确声明与状态）

| 依赖 | 文件/声明 | 状态 |
|---|---|---|
| `PrimeGeFive` | IUT 基础定义 | 已存在 |
| `SourceDefinition31Data` | LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Boundary.lean:660 | 已存在，字段是原文输入 |
| `SourceHodgeTheaterFamily` | LeanFormal/IUT/IUTI/HodgeTheater/SourceHodgeTheaterFamily.lean:32 | 已存在 |
| `HodgeTheater` | LeanFormal/IUT/IUTI/HodgeTheater/HodgeTheaterCore.lean:31 | 已存在 |
| `OriginalInput` | LeanFormal/IUT/IUTIII/Theorem311/SourceOriginalInput.lean:41 | 已存在；唯一允许 input contract |
| `SourceTheorem311Realization` | LeanFormal/IUT/IUTIII/Theorem311/SourceHodgeTheaterBridge.lean:910 | 已存在；链内 produced target |
| `SourceLogShellDatum` | LeanFormal/IUT/IUTII/Kummer/SourceLogShellCarrier.lean:86 | 已存在；C2 donor |
| `SourceImageRealization` | LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceImageHull.lean:161 | 已存在；C3 donor |
| `StepXIContract` | LeanFormal/IUT/IUTIII/Corollary312/StepXI/Contract.lean:32 | 已存在；下游 consumer only |
| `Cor312ToABCBridgeInterface` | LeanFormal/IUT/ABCBridge/Bridge/Cor312ToABCBridgeInterface.lean | 已存在；C10 downstream |

C0 不新增同义 input/output 类型。它只应引用这些真实定义，并在 stage 2 中用真实字段组合。

## 6. proof_dependencies（证明责任）

| 节点 | 目标 | 状态 |
|---|---|---|
| C1 | 同一数域/地方与 strip/Frobenioid/theater 的实际对象比较 | gap |
| C2 | 实际 log/Kummer、核/像、Kummer 箭头、作用下降、K1/K2 | gap |
| C3 | 实际 q/theta-pilot、Kummer 表示、张量/区域落点、改根相容 | gap |
| C4 | 实际受约束选择/求值/可能像与 Ind 律 | gap |
| C5 | 实际 IPL/SHE/APT 算法相容 | gap |
| C6 | 原文局部/packet/procession 权重与归一化 | 部分 donor: Group6Normalization 局部换算 |
| C7 | 实际 λO-hull、共同控制、正有限体积 | 部分 donor: LocalFieldProductHull |
| C8 | 实际 determinant/arithmetic degree/Ob3-3 | gap |
| C9 | 实际 q 输出/逼近，消去 hq | gap |
| C10 | 总装配 | gap; file not created |

没有已证 C1–C10 的实际源定理；C0 不能把它们的结论作为输入。

## 7. 自然语言证明责任（C0 规格本身）

C0 的自然语言证明不是数学定理证明，而是使整链可表达：
1. 对任意 `I : OriginalInput l V`，C1 从 `I` 绑定同一数域、地方、strip/Frobenioid/theater；
2. C2/C3 从 C1 的同一输入构造实际 log/Kummer 与 q/theta-pilot；
3. C4 用实际选择和求值定义 `U`，保留内部见证；
4. C5 从同一算法构造 IPL/SHE/APT 相容；
5. C6/C7 用实际权重/λO-hull 得到归一化体积与共同控制；
6. C8 构造相对 determinant/tensor 幂/arithmetic degree；
7. C9 构造 Values 并证明 bound + q approximation，或直接 Q∈Values；
8. C10 组装并输出实际源 3.11、IPL/SHE/APT、hull/有限性、degree 和 Q≤Θ。

C0 只声明第 1 步的接口及输出角色；每一步的准确命题在 C1–C10 的 stage-1 记录中给出。

## 8. Mathlib / 项目 donor 搜索

已检查并应复用：
- `SourceOriginalInput.lean`：`OriginalInput` 与 `SourceTheorem311Index`；
- `SourceHodgeTheaterBridge.lean`：`SourceTheorem311Realization`；
- `SourceLogShellCarrier.lean`：`SourceLogShellDatum`、`logMap`、`preLogShell/logShell/unitLayer`；
- `SourceImageHull.lean`：`SourceImageRealization`、`sourceThetaPilotPoint`、`sourceHullVolume`、`sourceLocalLogDegree`；
- `LocalFieldProductHull.lean`：紧闭包 hull、measure_hull_pos_lt_top；
- `FinitePlaceNormalizedUnitScalingLogVolume.lean` 与 `Group6Normalization.lean`：局部归一化；
- `Cor312ToABCBridgeInterface.lean`：下游接口。

搜索未发现：
- 实际 IPL/SHE/APT 算法相容的精确 Lean 类型；现有 `StepXIContract` 的 ipl/she/apt 是自由 Prop。
- 实际 constructive multiradial Output 类型；`MultiradialKernel.Output` 的 `possibleImage` 是自由字段。
- 实际 arithmetic-degree/Ob3-3 的精确类型；`DetTensorPowerLogVolumeBookkeeping` 的 logVolume/tensorPower 是自由数据。
- 实际 q-pilot/theta signed 值的统一 source type；`sourceThetaPilotPoint` 与 `sourceHullVolume` 是现有真实 donor，但 C0 尚未把它们组合成源 q/theta 读出。

## 9. 精确缺口

1. C0 不能把整个输出包成一个 `N8TargetSpec` 无说明谓词；每个输出字段必须有真实类型/来源。
2. 当前没有非平凡的 IPL/SHE/APT 源算法类型，不能把 `StepXIContract.ipl/she/apt` 作为输出字段。
3. 当前没有 constructive multiradial output 类型；`Output` 的自由 possibleImage 不能作为 C4 输出见证。
4. 当前没有实际 Ob3-3 arithmetic-degree 类型；`DetTensorPowerLogVolumeBookkeeping` 是自由 bookkeeping。
5. `OriginalInput` 本身仍需 C1 审查实际 V/prime-strip/completion 绑定；C0 不能假定它已忠实覆盖所有原文输入。
6. C8/C9/C10 文件尚不存在；C0 仅冻结角色和消费者。
7. 任何 C0 Lean 签名若使用 `Nonempty`/`True`/自由字段，均违反 [SORRY-POLICY](SORRY-POLICY.md) 与 route §4/C0。

## 10. 验收与停止边界

- 本阶段交付：本 stage-1 记录；不交付 Lean C0。
- 未运行/未通过：C0 `statement_compiles` 尚未审核；`TargetSignature.lean` 为已丢弃 trial，不可作为证据。
- 停止边界：C0 stage1 审查通过后，才写 C0 Lean 签名；签名必须引用真实定义并逐字段给出 source/consumer/gap。
- 下一步：交给 C0 reviewer 审核本记录，确认 input/output 角色及 C10 consumer 后再开 stage 2。

## Label 结构更正（2026-10-23）

原文 label 是有限集合 S_{j+1} + arbitrary permutation automorphisms（IUT III corpus 544-570），不是 `AddGroup Label`。C0 的 `[AddGroup Label]` 只是 `SourceTheorem311Realization` 的生产索引表示，不是原文 label 语义。C0 stage2 必须用 `LabelData`/procession label，或把 production additive index 与 label set 的显式比较作为独立 obligation。
