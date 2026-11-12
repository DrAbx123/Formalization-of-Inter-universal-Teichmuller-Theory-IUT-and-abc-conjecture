# UNIFIED OBJECTS A502 — 自有 + Takkun 合并对象骨架

依据：`coord/OWN-ASSETS-STATUS-A502.md`（自有对象层薄：Hodge 16/LogShell 8/InitTheta 1；ThetaLink/Lattice/Multiradial 定义 0）+ `coord/TAKKUN-OBJECT-MAP.md`（Takkun 有 LogShell/LogLink/LogChain/LogThetaLattice/FhPrimeStrip/PrimeStripSystem）。只合并**真实定义**，不碰空壳文件（`Mzk1ThetaLinkInterfaceActual.ThetaLinkData`、`Mzk1LogThetaLatticeActual.LogThetaLattice(lattice:Prop):=lattice`、`InitialThetaData : Prop`）。

## 合并原则

- **自有为主**：Hodge theater 三件套（`HodgeTheaterCore.HodgeTheater`）、prime strips（`PrimeStripCore.DPrimeStrip/FPrimeStrip`）、log-shell 载体、hull/Haar/det（我们自己的 HolomorphicHull/literal 层）。
- **Takkun 补缺**：`LogShell/LogLink/LogChain/LogThetaLattice`（lattice/link 骨架）、`FhPrimeStrip/GaussianPrimeStrip/PrimeStripSystem`（标签化素点縞与 θ 值）、`Full`（Θ±ellNF 贴合数据）。
- **适配方向**：自有 `FPrimeStrip` → Takkun `FhPrimeStrip`（已有 adapter，`Mzk1TakkunPrimeStripAdapterActual.takkunFhOfOur`）；Takkun 对象只作为对象字段进入统一骨架，不反向覆盖自有定义。
- Takkun `UpperSemiCompatibility` = orbit 恒真（A500 审计），只用其 `LogShellIndeterminacy` 的**作用数据形状**，不采纳其 Ind3 结论。

## 映射表（O1–O12）

| O | paper 对象 | 自有真实对象（file:decl） | Takkun 对象（file:decl） | 统一骨架（本文件字段） | 状态 |
|---|---|---|---|---|---|
| O1 | BPS / D-F-prime-strip | `IUTI/HodgeTheater/PrimeStripCore.lean:24 DPrimeStrip`、`:117 FPrimeStrip`（+Equiv） | `Frobenioid/PrimeStripSystem.lean:159 DhPrimeStrip`、`:203 FhPrimeStrip`、`:214 Equiv`、`:449 LabeledPrimeStripSystem` | `UnifiedMultiradialSkeleton.fh : FhPrimeStrip`（由自有 `hodge.primeStrip` 经 adapter） | 合并中（自有+adapter） |
| O2 | multiradial algorithm 环境 | 无（自有缺口） | `LogTheta/LogShell.lean LogShell/LogLink/LogChain`；`LogTheta/Lattice.lean LogThetaLattice`（ℤ×ℤ→Full） | `lat : LogThetaLattice`, `logChain : LogChain`, `shell : LogShell` | Takkun 骨架（真实定义） |
| O3 | mlt representation / Θ±ellNF Hodge theater | `HodgeTheaterCore.lean:31 HodgeTheater`（+`:36 HodgeTheaterLink`、ThreeTheaterSystem、Concrete 例） | `HodgeTheater/Defs.lean:36 AdditiveHodgeTheater`、`:49 Multiplicative`、`:63 Full`；`HodgeTheater/PrimeStripData.lean:38 PrimeStripSystem` | `hodge : HodgeTheater l V` + `lat.HT` 的 `Full` 节点 | 合并中（自有 theater + Takkun Full/lattice） |
| O4 | dsc + Ind1/2/3 | `Theorem311/Indeterminacy/Ind1Reduction.lean Ind1Setoid/Ind1DescentData`；`Ind1ActionLawsActual.Ind1UnitAction` | `LogTheta/Indeterminacy.lean LogShellIndeterminacy`（Γ-action 数据；`UpperSemiCompatibility` 为 orbit 恒真，仅取形状） | 字段 `indet : LogShellIndeterminacy`（可选，仅数据） | 自有 Ind1 真实；Ind2/3 仍缺口 |
| O5 | etHT / θ 值 / Kummer | （自有 log-shell 载体：`SourceLogShellCarrier.logShell`、`SourceProcessionCapsuleData.LogShellFamily`） | `GaussianPrimeStrip`（qParam/thetaValueAt/± 对称）、`PrimeStripSystem.kummer`（円分指標） | `fh` 的 Mon/θ 值经 Takkun Gaussian 层可扩展 | Takkun 真实引理可用 |
| O6 | 0-column / etHT transport | 无 | `LogThetaLattice.thetaColumn`/`logRow`、`ThetaChain` | `lat.thetaColumn 0`/`logRow 0` | 骨架（无相容性证明） |
| O7 | hull | 自有 HolomorphicHull（`LocalFieldProductHull`、literal `litHull`、`literalGlobalIQHull_measure_lt_top`） | 无 | 不并入（自有 lane 继续） | 自有真实 |
| O8 | det | 自有 `HullDeterminantLogVolumeReduction`（PositivePacket/matrixLogDet/packetLogVolume） | 无 | 不并入 | 自有真实 |
| O9 | Holomorphic hull | 自有 `HolomorphicHull/*`（Haar/procession 平均/compactness） | 无 | 不并入 | 自有真实 |
| O10 | HDD 分解 | 自有 `Mzk1FourTriangleSharedActual.HDDDecomp/FourTriangleSynthesis`（泛型，已被 A497 审计为函数级抽象） | 无 | 不并入 | 仅骨架接口 |
| O11 | SHE | 自有 `Mzk1QPilotSHEDoubleImageActual.SHEArrowStatement`（真实：θ^{2l}=q 的坐标方程） | 无 | 不并入（独立） | 自有真实（局部） |
| O12 | q/Θ 比较（Cor 3.12） | 无（qTheta 链已 VOID；真缺口 hcomp 两条 IUT IV 比较） | 无 | 不并入 | 缺口 |

## 统一骨架文件（1 个 `_constructed`）

`tmp/sheaf/xif/paper/Mzk1UnifiedObjectSkeletonActual.lean`（import 自有 HodgeTheaterCore/PrimeStripCore + Takkun FhPrimeStrip/PrimeStripSystem/LogShell/Lattice/Indeterminacy/Defs + 上一 adapter）：

- `UnifiedMultiradialSkeleton (l) (V)` 字段：`hodge : HodgeTheater l V`、`fh : FhPrimeStrip V`、`lat : LogThetaLattice`、`logChain : LogChain`、`shell : LogShell`、`thetaChain : ThetaChain V`；
- `unifiedSkeletonOf hodge lat logChain shell thetaChain : UnifiedMultiradialSkeleton` —— 从**真实数据参数**构造（`fh := takkunFhOfOur hodge.primeStrip`，其余字段直接赋予），非接口占位；
- `_constructed` 定理族：
  - `unifiedSkeleton_fh_constructed`：`fh = takkunFhOfOur hodge.primeStrip`（rfl，走 adapter）；
  - `unifiedSkeleton_shell_carrier_constructed`（def）：`AddCommGroup shell.carrier`（`inferInstance`，真实实例）；
  - `unifiedSkeleton_logLink_one`：对任意 `LogLink U shell`，`logMap (ofMul 1) = 0`（复用 Takkun 已验证 `LogLink.logMap_one`）；
  - `unifiedSkeleton_lattice_columns`：`lat.thetaColumn n m = lat.HT (n,m)`、`lat.logRow m n = lat.HT (n,m)`（rfl，复用 Takkun `LogThetaLattice` 定义）。

## 状态与后续

- 统一骨架只覆盖 **O1/O2/O3/O6 的对象形状**；O4 Ind2/3、O7–O9 保留自有 lane；O10–O12 缺口不变。
- 下一步（对象优先）：用自有 `FPrimeStrip`/`HodgeTheater` + Takkun `PrimeStripSystem`/`GaussianPrimeStrip` 构造**具体** `Full`（Θ±ellNF）实例并证明 `_constructed` 的 glue/nondegenerate 字段成立；然后才允许四三角合成。
## A504 修订：统一骨架改为**真实构造模型**（不再是参数包 wrapper）

lattice 审计指出旧 `unifiedSkeletonOf` 是全参数 identity wrapper，已重写为 `unifiedSkeletonModel l : UnifiedObjectSkeleton l`，字段全部取具体对象：

| 字段 | 取值（真实对象） | `_constructed` |
|---|---|---|
| `hodge` | `LeanFormal.IUT.gaussianHodgeTheater l`（自有 core 的 concrete 例：gaussianInitialThetaArithmeticData + localFPrimeStrip + FiniteThetaPacket.ofQ 1/2） | `unifiedSkeletonModel_hodge` (rfl) |
| `fh` | `takkunFhOfOur (gaussianHodgeTheater l).primeStrip`（adapter 真实像） | `unifiedSkeletonModel_fh` (rfl) |
| `theaterFull` | `IUT.Arithmetic.realHodgeTheater`（实曲线 11a3：q=11，Gaussian θ 值 q^{j²}） | `unifiedSkeletonModel_theaterFull` (rfl) |
| `concreteLattice` | `realConcreteLattice : LogThetaLatticeConcrete.{0} RationalPlaces` —— core=`realDStrip.G`、thetaLink=refl、unit=`ℚ_[11]ˣ`、shell=`realLogShell=ℤ_[11]`、logLink=`realLogLink`（p 进赋值 log map） | 定义即真实数据 |
| `lat` | `{ HT := fun _ => realHodgeTheater }` | — |
| `logChain` | `realConcreteLattice.logColumn 0` | `unifiedSkeletonModel_logChain_shell` (rfl) |
| `thetaChain` | `realConcreteLattice.thetaRow 0` | `unifiedSkeletonModel_thetaChain_core` (rfl) |
| `shell` | `IUT.Arithmetic.realLogShell` | `unifiedSkeletonModel_shell`、`_shell_carrier_constructed`（`AddCommGroup ℤ_[11]` 实例） |

另有真实数值复算：`unifiedSkeletonModel_logMap_qParam`（复用 `realLogMap_qParam : v₁₁(11)=1`）、`unifiedSkeletonModel_logLink_one`（复用 Takkun `LogLink.logMap_one`）、`unifiedSkeletonModel_nonempty : Nonempty (UnifiedObjectSkeleton l)`。
文件：`tmp/sheaf/xif/paper/Mzk1UnifiedObjectSkeletonActual.lean`（**收窄 import**：自有 ConcreteHodgeTheaterExample + Takkun `LogTheta/{LogShell,Lattice,LatticeConcrete}` + `Arithmetic/RealHodgeTheater` + adapter；不再 import 重的 `Arithmetic/IntegrationTest`——log shell `ℤ_[11]` 与 valuation log-link `u↦v₁₁(u)` 本地构造 `modelLogShell/modelLogMap/modelLogLink`，`modelLogMap_qParam : v₁₁(11)=1` 独立证明复用 `Padic.valuation_*`）。