# A502 我们自己的 LeanFormal / tmp 资产盘点（对象层）

## 扫描口径（定义级关键词匹配，排除 .lake/.git）
- `LeanFormal/IUT`：1,187 文件、5,541 个 structure/def/class；对象关键词命中：Hodge 16、LogShell 8、InitTheta 1、Pilot 1、Indet 1；**ThetaLink/LogLink/Lattice/Multiradial 定义 0**
- `tmp/sheaf/xif/paper`：16,031 文件、22,940 定义；命中：Pilot 15、HullDet 8、InitTheta 4、LogShell 2、ThetaLink 1（Prop）、Lattice 1（**`def LogThetaLattice (lattice : Prop) : Prop := lattice` 空壳**）、Multiradial 1
- `tmp/sheaf` 全部：18,524 文件、28,951 定义；InitTheta 22、Lattice 19、Pilot 18（含 Takkun 移植）
- 根 `Iut/`：256 文件、0 sorry，仅 Foundations（anabelian/来源层）

## 真实可用的自有对象（示例）
- **Hodge theater 核心**：`IUTI/HodgeTheater/HodgeTheaterCore.lean:31 structure HodgeTheater (l) (V)`、`structure HodgeTheaterLink`（refl/symm/trans 已证）、`structure ThreeTheaterSystem`；concrete gaussian 例（`ConcreteHodgeTheaterExample`）
- **prime strips**：`PrimeStripCore.lean:24 DPrimeStrip`、`:49 DhPrimeStrip`、`:58 DhPrimeStripEquiv`
- **log-shell 载体**：`SourceLogShellCarrier.lean:124 def logShell (D : SourceLogShellDatum) : Set D.K`；`MonoAnalyticLogShellCompactCarrier.logShell`；`SourceProcessionCapsuleData.LogShellFamily`
- **hull/Haar**：literal `litHull/litUnitRegion/litHaar`、`literalGlobalIQHull_measure_lt_top`、`HullDeterminantLogVolumeReduction`、`S3137/AbsTopIII09` 的 C3 Haar log-volume
- **Ind1 作用**：`Ind1ActionLawsActual` 的 `Ind1UnitAction`

## 仅接口/空壳（不能当对象；已在 gate 标注）
- `InitialThetaData` = **Prop 缩写**（SourceDefinition31Quantifiers:1732）
- `Mzk1ThetaLinkInterfaceActual.ThetaLinkData (S T)` 字段为 `left_inv/right_inv` = **等价/双射**，不是 Θ-link
- `Mzk1LogThetaLatticeActual`：`LogThetaLattice (lattice : Prop) := lattice` **空壳**
- `HDDDecomp/FourTriangleSynthesis`：函数级抽象，无 hull/det 真实对象
- 大量 `*Obligation`、`*PaperInput`、`*PaperStmt`：陈述记录，非构造

## 与 Takkun 的互补关系
- 我们有：HodgeTheater/prime strips/log-shell 载体/hull/Haar/Ind1 作用 —— Takkun 弱或没有
- Takkun 有：`LogShell/LogLink/LogChain/LogThetaLattice`、`FhPrimeStrip`、`PrimeStripSystem`、Θ 值 ± 对称、`gaussExp`、`aRadius/bRadius/logVol/logVol_pow`、`ThetaValues` —— 我们缺
- 因此对象层 = 自有真实基础 + Takkun 对象定义（移植 `tmp/sheaf/takkun/`），逐个适配/审计后合成

## 下一步
1. 审计并升级自有空壳（ThetaLinkData/LogThetaLattice）为真实对象或删除
2. 合并：自有 HodgeTheaterCore/PrimeStrip ↔ Takkun `FhPrimeStrip`/`PrimeStripSystem`（mainline 已有第一个 adapter）
3. 用 Takkun `LogTheta/*` + 自有 log-shell 载体构造 log-theta lattice 与 Θ-link/log-link 对象
4. 全部对象 `_constructed` 后再合成四三角