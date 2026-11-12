# A505: 联合地基 vs O1–O12 对象缺口覆盖表（只读）

来源: `coord/UNION-FOUNDATION-A505.md`（地基清单/工具）、`coord/UNIFIED-OBJECTS-A502.md`（O1–O12 映射）、`coord/OBJECT-FIELD-DIFF.md`/`OWN-OBJECT-FAITHFULNESS.md`（字段级核对）、Takkun 68 模块状态（A504: 23/68 olean，`Padic/LogShellRadius` OOM）。只读；本文件不新增壳/不改队列。

## 1. 地基分层（可 import 的层）

| 层 | 内容/路径 | 对 IUT 对象的作用 | 状态 |
|---|---|---|---|
| L0 Mathlib v4.32.2 | 当前 lake require | 数域/p 进/代数闭包/Haar/测度/线性代数/椭圆曲线/实数分析等全部底料 | 已编译可用 |
| L1 local-cft-port | `tmp/local-cft-port`：PadicField/Reciprocity/ClassFieldAxiom/Galois/Herbrand/Brauer/ContinuousKummerTheory | 局部类域论、Brauer、连续 Kummer（O5 Kummer 类、O12 算术侧） | 已注册 lake lib；oleans 按需入队 |
| L2 ported TauCeti | `tmp/external/ported/tauceti*`（tauceti2 264、rr 263、belyi_rr 183、belyi_ff 174、belyi_core 6） | 高度/Belyi/数论估计；不提供 IUT 对象本身 | 已脚本移植，import 已改写；按需入队闭包 |
| L3 ported Fermat | `tmp/external/ported/flt*`（flt 19、flt_core 234、flt_th 239、flt_test 224） | 椭圆曲线/算术几何/高度（O12 的 ABC 应用侧） | 同上 |
| L4 ported Belyi | `tmp/external/ported/belyi*`（belyi_pair 276、pair_scheme 276、poly 5） | Belyi/曲线构造（anabelian/hyperbolic 侧辅助） | 同上 |
| L5 Takkun-IUT_LEAN | `tmp/sheaf/takkun/IutLean/`（68 模块）：Frobenioid.Model/PrimeStrip/loc、FhPrimeStrip、GaussianPrimeStrip、PrimeStripSystem、LogShell/LogLink/LogChain/LogThetaLattice/Indeterminacy、ThetaValues、RealFrobenioid/RealHodgeTheater/RealKummer | IUT 对象层的主要外部来源（对象+已验证引理；结论按 A500 只作待审计数据） | **编译中 23/68**；`Padic/LogShellRadius` OOM 需收窄 import |
| L6 自有 | `LeanFormal/IUT`（1,187；HodgeTheaterCore/PrimeStripCore/SourceLogShellCarrier/LogShellFamily/Ind1Action/HolomorphicHull/literal IQ carrier/Haar）、根 `Iut/`（256 Foundations）、`tmp/sheaf/xif/paper`（HDD/SHE/qTheta 等） | O1/O3/O4/O7/O8/O9/O11 的真实/骨架资产 | 真实对象见 OWN-OBJECT-FAITHFULNESS.md；qTheta 链 VOID |
| L7 待移植 | promachina 200、iut4-sec1、PriestAmbrose | 暂不计入覆盖 | 未移植 |
工具: `tools/extras_add_closure.mjs <files...>` 从目标文件算 import 闭包入队（lock/去重/原子）；**不得**手写基础，缺则从以上层 grep 复用。

## 2. O1–O12 覆盖矩阵

图例: **✓覆盖**（地基+已有对象即可构造对象本身）；**△部分**（对象形状可得，关键相容/传输/归一化定理仍需造）；**✗缺口**（联合地基不覆盖，必须从对象构造/数学内容）。

| O | paper 对象 | 需要的 ingredients | 覆盖层与具体 decl | 判定 |
|---|---|---|---|---|
| O1 | BPS / D-F-prime-strip | 每 place 群 Π_v/G_v、proj、F-值幺半群+作用+degree、F⊢/Fh/Gaussian、全局实化 Frobenioid | 自有 `PrimeStripCore.lean:24 DPrimeStrip`、`:117 FPrimeStrip`(+Equiv)；Takkun `Frobenioid/PrimeStrip.lean:22 PrimeStrip{loc:V→Model}`、`PrimeStripSystem.lean:71 FPrimeStrip`、`:159 DhPrimeStrip`、`:203 FhPrimeStrip`、`:214 FhPrimeStripEquiv`、`:449 LabeledPrimeStripSystem`、`HodgeTheater/PrimeStripData.lean:85 PrimeStripSystem`；Mathlib 群/幺半群/Model 无（Frobenioid.Model 由 Takkun 提供） | **✓覆盖（对象层）**：自有+adapter 已有 `Mzk1TakkunPrimeStripAdapterActual.takkunFhOfOur`；F⊩=F⊢+global realified 仍需把 Takkun `PrimeStrip.loc`+global realified 补上（Takkun 提供 Model；global realified 在 Takkun 的 F⊩ 层/`Frobenioid/Basic` 需核对） |
| O2 | multiradial algorithm 环境 | 0-column、log-theta lattice、log-link 链、log-shell 链 | Takkun `LogTheta/LogShell.lean:22 LogShell`、`:32 LogLink`、`:59 LogChain`；`LogTheta/Lattice.lean:22 LogThetaLattice`；`LatticeConcrete.lean:31 LogThetaLatticeConcrete`；自有 `HodgeTheaterCore` | **△部分**：环境对象形状 ✓（Takkun 真实定义）；但 multiradial algorithm Steps 1–9 的构造性算法/相容性 ✗（Takkun 仅骨架，且 `UpperSemiCompatibility` 审计为 orbit 恒真，不用其结论） |
| O3 | mlt representation / Θ±ellNF Hodge theater | Θ±ell/ΘNF 分解、prime-strips system、glue、label symmetry、gaussian、histories | 自有 `HodgeTheaterCore.lean:31 HodgeTheater`（+link/ThreeTheaterSystem/Concrete 例）；Takkun `HodgeTheater/Defs.lean:36/49/63 Additive/Multiplicative/Full`、`PrimeStripData:85 PrimeStripSystem`、`Symmetry.lean`、`Arithmetic/RealHodgeTheater.lean realHodgeTheater/realDStrip/realGaussianStrip/realPrimeStripSystem`；Mathlib 椭圆曲线/局部域 | **✓覆盖（具体/实例）**：`realHodgeTheater`（q=11 实例）+ 自有 gaussian 例可拼 Full；**一般 gluing/nondegenerate 条件**需构造（字段 glue/label symmetry 的证明）。可先用 L5 的 RealHodgeTheater 作 anchor。 |
| O4 | dsc + Ind1/2/3 | Ind1 setoid/descent/action、Ind2、Ind3 上半相容、dsc 映射 | 自有 `Theorem311/Indeterminacy/Ind1Reduction`（Ind1Setoid/Ind1DescentData）、`Ind1ActionLawsActual`（polyIso/tprod 律）；Takkun `LogTheta/Indeterminacy.lean:46 LogShellIndeterminacy`（Γ-action 形状；A500 审计不采纳其 Ind3 结论） | **△部分**：Ind1 真实对象 ✓（label permutation+component equiv）；Ind2/3 与 dsc 具体映射 ✗（无地基提供；Takkun 只有数据形状，Ind3=orbit 恒真不可用） |
| O5 | etHT / θ 值 / Kummer 类 | q 的 2ℓ-根、theta 值 q^{j²} 在 Mon/Galois 下、Kummer 类/1-cocycle、円分指標 | Takkun `Theta/ThetaValues.lean:23/45`、`PrimeStripSystem.lean:309 GaussianPrimeStrip`（qParam/thetaValueAt）、`Cyclotome/Kummer.lean`、`Arithmetic/RealKummer.lean`（realQRootSystem/realQKummer_cocycle/realThetaKummer/realThetaKummer_cocycle）、`RealHodgeTheater.lean`（galoisUnitsAction）；L1 ContinuousKummerTheory；自有 `SourceLogShellCarrier`/`SourceProcessionCapsuleData.LogShellFamily`；Mathlib 代数闭包/p 进 | **✓覆盖（对象层，用 Takkun 真实构造）**：RealKummer+RealHodgeTheater 提供实际 q=11 的根/Kummer 类；theta 值的 Mon 版本可用；**一般/paper-level 的 q_v (2ℓ root) 与 Ind 相容性**需构造（A497/S342 提醒：completion 内无根，须扩张）。 |
| O6 | 0-column / etHT transport | thetaColumn/logRow/0-column、ThetaChain、coricity transport | Takkun `LogThetaLattice.thetaColumn/logRow`（定义）+ `ThetaChain`（PrimeStripSystem:337）；自有无 | **△部分**：0-column/chain 对象形状 ✓（Takkun 定义）；**transport/coricity 相容性** ✗（无证明；Takkun 只有定义） |
| O7 | hull（least region a·O / packet hull） | 局部域张量 hull、λ-O hull、compactness | 自有 `HolomorphicHull/*`（`LocalFieldProductHull`、literal `litHull`、`literalGlobalIQHull_measure_lt_top`、`SourceHullCompactnessReduction`）；Mathlib Haar/compact/proper；Takkun 无（RealHodgeTheater 只有 qParam） | **✓覆盖（自有真实）**：hull 对象与 finiteness 已有；**Θ-pilot-specific hull（union over possible images/Ind）** 需在 O2/O3 之后构造（当前 hull 是 literal IQ/Haar 层，不是 paper Θ-pilot hull；A498/A502 已注）。 |
| O8 | det | PositivePacket、matrixLogDet、packetLogVolume、det 线归一化 | 自有 `HullDeterminantLogVolumeReduction`；Mathlib 线性代数/det/Matrix | **✓覆盖（自有真实）**：det/体积归约已可复用；与 O7 的 hull/det 合成（HDD 部分）见 O10。 |
| O9 | Holomorphic hull（Haar/procession 平均/compactness） | Haar 测度、log-volume、j∈F_l^⋇ 平均、Q-span/tensor | 自有 `HolomorphicHull/*`（Haar/procession average/compactness）、`C3LogShellTensorPacketActual`/`S3137`/`AbsTopIII09`（C3 Haar log-volume）；Mathlib MeasureTheory/AddHaar | **✓覆盖（自有真实）**：Haar/hull/平均工具真实；**注意**：`Measure.addHaar` up-to-constant（A498）；procession 平均须按 paper l−1 而非 l（A498/A497） |
| O10 | HDD 分解（hull+det 复合） | hull、det、common container/ring、HDD=(hull+det)∘dsc | 自有 `Mzk1FourTriangleSharedActual.HDDDecomp/FourTriangleSynthesis`（A497 审计：函数级抽象，非对象）；Takkun `LatticeConcrete`/`Cor312` 的 HDD 骨架（待审计数据，不作证明） | **✗缺口（对象级）**：地基不提供；须用 O7+O8 的 hull/det 真实对象 + O2/O3 的 theater/dsc 构造 HDD 复合；不得以函数级抽象充当。 |
| O11 | SHE（simultaneous holomorphic expressibility） | q-pilot 由 etHT 构造、Θ-link 的 Hodge/Holomorphic transport | 自有 `Mzk1QPilotSHEDoubleImageActual.SHEArrowStatement`（θ^{2ℓ}=q 的坐标方程；局部真实）；Takkun `Multiradial/Cor312`/`LogTheta/LogKummer`（待审计）；Mathlib 代数几何无 SHE | **△/✗**：局部 SHE 方程 ✓（自有）；**paper SHE 的 Hodge theater transport** ✗（无地基；须以 O3+O5 构造）。 |
| O12 | q/Θ 比较（Cor 3.12） | Θ-pilot hull log-volume、q-pilot |log q|、finiteness、C_Θ、hcomp 两条 IUT IV 比较 | 自有：无（qTheta VOID）；Takkun `Multiradial/Cor312`/`Thm110`（形式骨架，含未证输入，外部数据）；Mathlib real/estimates；L2/L3 高度/Belyi 只助 ABC 应用侧 | **✗缺口（核心数学）**：联合地基不覆盖；需先 O7/O9 的真实 Θ-pilot hull/procession 对象 + q-pilot |log q|（含 2ℓ 归一化）→ 再证 hcomp 两条 IUT IV 比较。Takkun 结论不可直接用作证明（A500）。 |

## 3. 覆盖汇总

| 覆盖等级 | O | 说明 |
|---|---|---|
| **✓ 地基+现有对象可构造对象本身** | O1、O3（具体/实例）、O5（用 Takkun Real*）、O7、O8、O9 | 可直接以自有+Takkun/Mathlib 组合，加 `_constructed` 定理（非参数 wrapper） |
| **△ 对象形状可得，相容/传输定理需造** | O2、O4-Ind1、O6、O11（局部）、O3（一般 gluing/nondegenerate） | Takkun 提供定义/骨架；证明需按 paper 补 |
| **✗ 联合地基不覆盖，必须真构造/数学工作** | O4-Ind2/3+dsc、O10、O11（SHE general）、O12、O7/O9 的 Θ-pilot-specific hull | 缺口集中：multiradial algorithm 的相容性、Ind2/3、HDD/SHE、Cor 3.12/hcomp |

**层次与对象的对应总结**: L0 Mathlib 提供所有底层数学（p 进/数域/Haar/线代/椭圆曲线）；L1 local-cft 只对 O5 Kummer/O12 算术侧有用；L2/L3/L4（TauCeti/Fermat/Belyi）**不提供 IUT 对象**，只对 O12 的 ABC 应用/高度估计/曲线几何有辅助；L5 Takkun 是 O1/O2/O3/O5/O6 对象层的主要来源（但结论按 A500 只作数据）；L6 自有对 O7/O8/O9 真实、O1/O3/O4-Ind1 真实骨架、O11 局部真实；O10/O12 无层覆盖。

## 4. 入队/编译建议（供 Lead 执行，不在本文件执行）

1. **Takkun OOM**: 当前 23/68 olean，`Padic/LogShellRadius` OOM，由 import `Mathlib.Tactic`（完整 tactic 包）导致；收窄为具体 tactic import（Linarith/Ring/NormNum/Positivity/GCongr + omega 所需核心）后重新入队（文件已在 extra-targets，mtime 更新即可重试）；其余 OOM 文件同法。
2. 按对象优先级入队闭包（用 `tools/extras_add_closure.mjs`）：
   - O5：`tmp/external/Takkun.../Arithmetic/RealKummer.lean`、`RealHodgeTheater.lean`、`Theta/ThetaValues.lean`、`HodgeTheater/PrimeStripData.lean`（含 `PrimeStripSystem`）闭包；
   - O1/O3：Takkun `Frobenioid/PrimeStrip.lean`、`PrimeStripSystem.lean`、`HodgeTheater/Defs.lean`、`Symmetry.lean` + 自有 `PrimeStripCore`/`HodgeTheaterCore`/adapter；
   - O2/O6：Takkun `LogTheta/{LogShell,Lattice,LatticeConcrete,Indeterminacy}.lean`；
   - O7/O8/O9：自有 `HolomorphicHull/*`、`HullDeterminantLogVolumeReduction`、`C3LogShellTensorPacketActual`；
   - O12：先把 O7/O9 的真实 hull 目标入队；hcomp 两条 IUT IV 比较需自造（无外部基础可复用）。
3. **空壳拦截**: 不把 `LogThetaLattice(lattice:Prop):=lattice`、`ThetaLinkData`=双射、`InitialThetaData:Prop` 当对象；入队前 grep 定义体，只接受有构造字段/`_constructed` 的文件。
4. **不要**用 TauCeti/Fermat/Belyi 的结论当 IUT 对象；它们只在 O12 应用侧（高度/ABC/Belyi）作算术工具。

## 5. 结论

联合地基 + 自有对象已足以**构造** O1/O3（具体/实例）/O5/O7/O8/O9 的对象本身；O2/O4-Ind1/O6/O11-局部只有形状/部分内容，需补相容性；O10/O12 与 O4-Ind2/3、一般 SHE 是真缺口，联合地基**不覆盖**，必须在对象构造完成后自证。O12 的 hcomp 两条 IUT IV 比较仍是最后的核心数学缺口（A497/A499 已定位）。

只读；未改任何文件/队列/watchdog。
