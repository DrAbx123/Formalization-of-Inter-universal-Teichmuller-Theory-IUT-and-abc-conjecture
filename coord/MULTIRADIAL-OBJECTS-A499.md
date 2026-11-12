# MULTIRADIAL OBJECTS A499 — O3 multiradial representation (Steps 1–9) 盘点

对象优先（不再 wiring-first）。本表仅盘点**现有 Lean 定义/构造**，标注：真实构造 / 结构定义（数据类）/ 接口/契约 / 缺失。
来源：`LeanFormal/IUT/IUTI`、`LeanFormal/IUT/IUTII`、`LeanFormal/IUT/IUTIII/Theorem311`、`.../Corollary312/StepXI/HolomorphicHull`（行号为当前文件）。

## 步骤映射（本文采用）

| Step | paper 内容（multiradial 构造） | 主要对象 |
|---|---|---|
| 1 | BPS / D-prime-strip 输入 | DPrimeStrip, FPrimeStrip |
| 2 | 初始 Θ-data（Definition 3.1） | SourceNativeInitialThetaData, InitialThetaArithmeticData |
| 3 | D-Θ±ellNF Hodge theater + Θ-link/log-link 历史 | HodgeTheater, HodgeTheaterLink, History |
| 4 | prime-strip/frobenioid 链与 procession | FPrimeStripLink/FPrimeStripLinkSystem, procession capsule |
| 5 | Θ-link / log-link（n→n+1） | HodgeTheaterLink/History（无独立 ThetaLink/LogLink 结构） |
| 6 | log-shell 族 + tensor packets + LGP monoid | LogShellFamily, TensorPacket, LGPMonoid |
| 7 | 多radial 环境 + Ind1/2/3 | Ind1Setoid/Ind1DescentData, Ind2/Ind3 certificate |
| 8 | q-pilot / Θ-pilot 对象与 possible images | ThetaPilotObject, ThetaPilotCarrier/ThetaPilotPoint, q-pilot 层 |
| 9 | log-volume / holomorphic hull on mlt rep | LocalFieldProductHull, TensorPacket volumes, IQHullLogVolumeInterface（接口） |

## Step 1 — BPS / D-prime-strip

| file:decl | 类型 | 状态 |
|---|---|---|
| `IUTI/HodgeTheater/PrimeStripCore.lean:24` `structure DPrimeStrip (V)` | 数据（每 place 群 Pi、商群 G、surjective proj） | **真实定义**（字段为数学数据） |
| `:61` `structure DPrimeStripEquiv` / `:166` `FPrimeStripEquiv` | ≃ 型结构 | 真实定义 |
| `:117` `structure FPrimeStrip (V) extends DPrimeStrip`（Mon/action/degree） | 数据 | **真实定义** |
| `:55` `DPrimeStrip.toDh` | 到 Dh-prime-strip 的转换 | 真实定义 |
| `IUTII/Frobenioid/PrimeStripDegree.lean:22` `structure PrimeStripDegree` | 度数据 | 真实定义 |
| `IUTII/Frobenioid/Example36PrimeStripComponentIdentification.lean:242` `structure PrimeStripComponent` | Example36 组件 | 有限模型（Example36） |
| `IUTIII/Theorem311/SourceFaithfulBoundary.lean:125` `ProcessionPacketProfile` 等 | source-faithful profile | 接口/数据混合（Source 层） |

**判定**：D/F-prime-strip **真实结构定义**存在；未发现“由具体曲线/数域构造 BPS”的构造定理（Example36 为单例有限模型）。

## Step 2 — 初始 Θ-data (Definition 3.1)

| file:decl | 类型 | 状态 |
|---|---|---|
| `IUTI/InitialTheta/SourceDefinition31Quantifiers.lean:1681` `structure SourceNativeInitialThetaData (l)` | 数据（大量字段） | **真实数据类**（字段承载 paper 数据） |
| `IUTI/InitialTheta/SourceDefinition31Quantifiers.lean:1732` `abbrev InitialThetaData (l) : Prop` | **Prop 化接口** | 接口（非构造） |
| `IUTI/InitialTheta/HodgeTheater/HodgeTheaterCore.lean:31` `HodgeTheater` 使用 `InitialThetaArithmeticData` | 数据 | 数据类 |
| `IUTI/InitialTheta/ConcreteInitialTheta*.lean`（CStage/FiniteArithmetic/Links/LocalArithmetic/Transport） | 具体构造 | **有限/具体模型构造**（Example 层） |
| `IUTI/InitialTheta/SourceDefinition31D2Root/D3D4Root/D4D9Supply/D5D8Root/*` | 定义 3.1 条件（D0–D11）拆解 | 接口/契约层（Source*） |

**判定**：`SourceNativeInitialThetaData` 是真实数据类；Definition 3.1 的 D0–D11 条件在 `SourceDefinition31*` 中多为**契约/接口**，Concrete* 为有限模型。

## Step 3 — D-Θ±ellNF Hodge theater + Θ-link 历史

| file:decl | 类型 | 状态 |
|---|---|---|
| `IUTI/HodgeTheater/HodgeTheaterCore.lean:31` `structure HodgeTheater (l) (V)` = arithmetic + FPrimeStrip + FiniteThetaPacket | 数据 | **真实定义**，但**只含 arithmetic/F/thetaPacket**，无 D-/D^>/D_< 分层与 ellNF 数据 → **部分对象** |
| `:36` `structure HodgeTheaterLink`（primeStripEquiv + theta q/scale 相等） | 数据 | 真实定义 |
| `IUTI/HodgeTheater/History.lean` `History`（θ-link n→n+1 历史） | 数据 | 真实定义（见文件） |
| `IUTI/HodgeTheater/LinkVolumeTransport.lean`（link 下的体积 transport） | 定理/数据 | 真实（有限模型） |
| `IUTI/HodgeTheater/ConcreteHodgeTheaterExample.lean` / `ConcreteIntegralHodgeTheaterExample.lean` | 具体 Hodge theater 实例 | **有限模型构造**（非一般 source 构造） |
| `IUTI/HodgeTheater/SourceHodgeTheaterFamily*.lean`、`SourceThetaLink*Reduction.lean` | family/θ-link（D-Θ±ellNF） | **接口/契约**（Source* 层，字段为 Prop/数据要求） |

**判定**：Hodge theater 的**三件套数据**真实；D-/D^>/D_< 与 ellNF 结构、一般 source 的 HodgeTheaterFamily、Θ-link 数据均为接口层。

## Step 4 — prime-strip/frobenioid 链与 procession

| file:decl | 类型 | 状态 |
|---|---|---|
| `IUTII/Frobenioid/PrimeStripsConstruction.lean:46` `structure FPrimeStripLink`；`:65` refl；`:75` trans | 链/复合 | **真实定义+reflexivity/trans 证明** |
| `IUTI/HodgeTheater/SourceHodgeTheaterFamilySourceReduction.lean:152` `structure FPrimeStripLinkSystem` | link system | 接口/数据 |
| `IUTII/Frobenioid/PrimeStripsFrobenioidLinks.lean:296` `FrobenioidValueKernel`；`:359` `PrimeStripFrobenioidLinkLayer` | frobenioid link 层 | 数据/接口（字段约束） |
| `IUTIII/Theorem311/SourceProcessionCapsuleData.lean:176` `structure LogShellFamily`；`:193–200` `DirectSumFactor`/`TensorPacket` | procession capsule 数据 | **真实定义** |
| `IUTIII/Theorem311/ConcreteFiniteModel.lean:98` `ProcessionChoice`；`:231/237` `Ind1Step/Ind3Step` | 有限 procession 模型 | 有限模型（真实证明） |

**判定**：prime-strip link（refl/trans）与 procession log-shell capsule/tensor packet 为真实定义；frobenioid link 层为数据/接口混合。

## Step 5 — Θ-link / log-link (n→n+1)

| 搜索证据 | 结果 |
|---|---|
| grep `^(structure\|def) ThetaLink` on `LeanFormal/IUT` | **0 命中** |
| grep `^(structure\|def) LogLink` on `LeanFormal/IUT` | **0 命中** |
| `IUTI/HodgeTheater/History.lean`（History 结构，需读字段） | 存在，承载 n→n+1 历史数据（待逐字段核） |
| `IUTI/HodgeTheater/HodgeTheaterCore.lean:36` `HodgeTheaterLink` | 单步 theater 链接（非对数 link） |
| `IUTIII/Theorem311/SourceThetaLink*Reduction.lean` | Source 层 θ-link 契约 |

**判定**：**没有独立的 ThetaLink/LogLink 构造对象**；只有 `History`/`HodgeTheaterLink` 数据与 Source 层契约。**缺失对象（Step 5 真实构造）**。

## Step 6 — log-shell 族 + tensor packets + LGP

| file:decl | 类型 | 状态 |
|---|---|---|
| `IUTIII/Theorem311/SourceProcessionCapsuleData.lean:176` `structure LogShellFamily (R) [CommSemiring R]` | 族数据 | **真实定义** |
| `IUTIII/Theorem311/SourceLogShellFamilyDependent.lean:58` `LogShellFamilyDependent`；`:73` `TensorPacketDependent` | 依赖族/tensor | 真实定义 |
| `SourceProcessionCapsuleData.lean:199` `abbrev TensorPacket (L) (vQ)` = ⨂ i, (v : Place vQ) → L.Shell i vQ v | 张量 packet | **真实定义** |
| `:205` `tensorPacketEquiv`、`:215` `tensorPacketEquiv_tprod` | 分布等价 + pure tensor 公式 | **真实定理** |
| `IUTIII/Theorem311/SourceLGPMonoidLayer.lean:64` `structure LGPMonoid (l)`（Carrier/splittingMonoid/thetaValueGenerator/closure 等式） | LGP monoid | **数据类，约束真实**；非从 q 构造 |
| `:154` `structure LGPMonoidAction`（actionOnTensorPacket） | action | 数据/真实定义 |
| `SourceLGPMonoidLayer.lean:218` `structure ThetaPilotObject`（generator + possibleImage = orbit） | Θ-pilot 有限模型 | **真实有限模型**（orbit 等式为字段） |

**判定**：log-shell 族/tensor packet/LGP monoid/action/ThetaPilotObject 为真实定义或有限模型；**LGPMonoid carrier 未从具体 q/Θ 值构造**（仅约束）。

## Step 7 — 多radial 环境 + Ind1/2/3

| file:decl | 类型 | 状态 |
|---|---|---|
| `IUTIII/Theorem311/Indeterminacy/Ind1Reduction.lean:96` `Ind1Setoid`；`:247` `Ind1DescentData` | Ind1 商/下降数据 | **真实定义**（Setoid/descent 数据） |
| `IUTIII/Theorem311/SourceFaithfulBoundary.lean:548` `Ind1Relation`；`:551` `Ind2Relation` | 关系定义 | 真实定义 |
| `IUTIII/Theorem311/ParametricCarrier.lean:272` `Ind2Certificate`；`:312` `Ind3Certificate` | Ind2/3 certificate | 数据/接口（certificate 字段） |
| `IUTIII/Theorem311/ParametricDStage.lean:73/125/214/240` `Ind2/Ind3 RouteCertificate` | 路线证书 | 数据/接口 |
| `IUTIII/Theorem311/ConcreteFiniteModel.lean:231/237` `Ind1Step/Ind3Step` | 有限模型步骤 | 有限模型（真实证明） |
| `IUTIII/Theorem311/Output/MultiradialAlgorithmReduction.lean`（`Core.ind1/ind2/ind3` 交换性定理） | 算法层 functoriality | **真实定理**（kernel 契约下） |

**判定**：Ind1 有真实 Setoid/descent；Ind2/Ind3 为 certificate/route 数据（接口 + 有限模型）；**没有**从 source 构造 Ind1/2/3 对象（paper 的 procession automorphism/Ism copies/upper-semi 层）。

## Step 8 — q-pilot / Θ-pilot 对象与 possible images

| file:decl | 类型 | 状态 |
|---|---|---|
| `IUTIII/Theorem311/SourceLGPMonoidLayer.lean:218` `ThetaPilotObject`（generator + possibleImage = orbit） | Θ-pilot 有限模型 | 真实（有限） |
| `IUTIII/Corollary312/StepXI/HolomorphicHull/SourceImageHull.lean:64` `ThetaPilotCarrier (l) : Type`；`:139` `ThetaPilotPoint (v) : Type` | Θ-pilot carrier/point | **真实具体载体**（源忠实层） |
| `IUTIII/Corollary312/ArithmeticQPilot*.lean`（`FinitePlaceQCandidate`, `localSignedLog`, `qNorm` 等） | q-pilot 局部数据 | **真实定义/定理**（局部 q 完成元素） |
| `SourceLGPMonoidLayer.LGPMonoidAction.actionOnTensorPacket` | 作用 | 真实定义 |
| `IUTIII/Theorem311/SourceFaithfulBoundary.lean` `ProcessionPacketProfile.possibleImage` 等 | possible image profile | 数据/接口 |

**判定**：局部 q-pilot 读法、Θ-pilot carrier/point、有限 orbit 模型为真实；**全局 Θ-pilot object**（paper 的 Θ-pilot divisor/zero locus）**缺失**。

## Step 9 — log-volume / holomorphic hull on mlt rep

| file:decl | 类型 | 状态 |
|---|---|---|
| `HolomorphicHull/LocalFieldProductHull.lean`（product hull/AdmissibleRegion） | 局部 product hull | **真实定义/定理**（含 compactness/volume） |
| `HolomorphicHull/LocalFieldIntegralHull.lean`、`LocalFieldProductHullBlocks.lean`、`LocalFieldPacketNormalizedVolume.lean` | hull 区块/归一化体积 | 真实定义/定理 |
| `HolomorphicHull/HaarTranslateRealLineProcessionAverage.lean` | procession 平均 Haar | **真实定理**（procession normalization） |
| `HolomorphicHull/HullDeterminantLogVolumeReduction.lean`（PositivePacket/matrixLogDet/packetLogVolume 等） | hull/det log-volume 演算 | **真实定义+定理**（frozen spec） |
| `HolomorphicHull/SourceHullCompactnessReduction.lean:52` `structure IQHullLogVolumeInterface` | hull/log-volume **接口** | 接口（字段抽象；hull_logVolume_lt_top 条件证明） |
| `ABCBridge/Geometry/FinitePlaceArithmeticIQTensor.lean:36` `arithmeticIQCarrier`；`SourceHullInterfaceDischarge`（F1/F2/F3） | literal 算术 IQ 载体 + 审计 | 真实（F2 证明 value-realization 障碍） |
| `tmp/.../litHull/litHaar`（A483） | literal 载体 product Haar | 真实（我们 lane） |

**判定**：局部 hull/体积、hull-det 演算、procession 平均为真实；**全局** `IQHullLogVolumeInterface` 仍为**接口**（载体实例在 literal/Example 层）。

## 汇总：真实 vs 接口/缺失

- **真实定义/构造（可直接复用）**：DPrimeStrip/FPrimeStrip(+Equiv)、HodgeTheater+HodgeTheaterLink（三件套数据、有限实例）、FPrimeStripLink(refl/trans)、LogShellFamily/DirectSumFactor/TensorPacket(+分布等价)、LGPMonoid/Action、ThetaPilotObject(有限 orbit)、Ind1Setoid/Ind1DescentData、LocalFieldProductHull/HullDeterminant 演算、Haar procession 平均、literal 算术 IQ 载体、`FinitePlaceQCandidate`/localSignedLog。
- **接口/契约层（非构造）**：`InitialThetaData : Prop`、`SourceDefinition31*`（D0–D11）、`SourceHodgeTheaterFamily*`、`SourceThetaLink*`、`Ind2/Ind3Certificate`、`IQHullLogVolumeInterface`、`SourceTheorem311*` 系列。
- **缺失对象（必须新建）**：
  1. **Step 5**：独立 Θ-link / log-link（n→n+1）对象（grep 0 命中；只有 History/HodgeTheaterLink 数据与 Source 契约）；
  2. **Step 3 补全**：D-/D^>/D_< 分层与 ellNF 数据的 Hodge theater（当前 HodgeTheater 仅三件套）；
  3. **Step 8 全局**：Θ-pilot object 的 source 构造（paper zero locus/arithmetic divisor 层）；q-pilot 的全局（非单点）构造；
  4. **Step 7 全局**：从 source 数据构造 Ind1/2/3（非 certificate 接口）；
  5. **Step 9 全局**：literal/global IQ carrier 上的 hull 有限性与 log-volume 归一化（R3 内容；当前为接口 + literal 模型）。

## 与 O3 任务的关系（明确边界）

- 本盘点只记录现有对象；`Mzk1HullDetNonVacuousSynthesisActual` 仅骨架（非 3.12 证据，且不依赖 qTheta 链）。
- 在三步对象（Step 5/3/8/7/9 缺失项）构造完成前，**不写四三角合成/3.11.5⇒3.12 证明**。