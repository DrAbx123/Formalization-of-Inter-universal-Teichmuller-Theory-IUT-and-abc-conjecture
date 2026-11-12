# A503: Takkun 对象 vs 自有对象 — 字段级差异（只读）

来源: `tmp/external/Takkun-IUT_LEAN/IutLean/`（原生；ported 在 `tmp/sheaf/takkun/`）与自有 `LeanFormal/IUT/...`。对标对象: InitialThetaData、HodgeTheater、PrimeStrip 层、LogShell/LogLink/lattice、Indeterminacy(Ind1-3)、ThetaValues，以及 Takkun 的 Real* 具体构造。只读；不新增壳/不改文件。

## 1. InitialThetaData vs InitialThetaArithmeticData

| | Takkun | 我们 |
|---|---|---|
| 位置 | `InitialThetaData/Defs.lean:39 structure InitialThetaData`（另有 `Deferred.lean` 用 opaque 处理部分条件） | `LeanFormal/IUT/IUTI/InitialTheta/ArithmeticData.lean:62 structure InitialThetaArithmeticData` |
| 字段数/内容 | F（Field/NumberField/DecidableEq）、sqrt_neg_one、E、E.IsElliptic、l（Nat）、l_prime、l_ge_five、lNeZero、stable_reduction、bad place 数据、contains_SL2_image 等（Def 3.1 (a)-(f) 的分项字段） | Fmod、F、K 三个数域 + Algebra/IsScalarTower/FiniteDimensional/IsGalois 实例、`tower : ThetaFieldTower`（含 sqrtNegOne、degreePrimeToL）、`curve : PuncturedEllipticCurve F` |
| 我们缺 | stable_reduction/bad-place/contains_SL2_image/ℓ 的显式字段（我们以 PrimeGeFive 参数携带 ℓ，并在 HodgeTheater/其它模块外置） | — |
| 赋值差异 | 单域 F + 条件 Prop 字段；l 是结构字段 | 三域塔（Fmod⊆F⊆K）作为结构字段；条件以 ThetaFieldTower 的 Prop 字段 + Audit interface 记录（未证存在） |

## 2. HodgeTheater

| | Takkun | 我们 |
|---|---|---|
| 结构 | `HodgeTheater/Defs.lean:40 AdditiveHodgeTheater`、`:52 MultiplicativeHodgeTheater`、`:66 Full`（=Θ±ellNF：`add`、`mul`、`glue : add.l = mul.l`） | `LeanFormal/IUT/IUTI/HodgeTheater/HodgeTheaterCore.lean:31 HodgeTheater`：`arithmetic`、`primeStrip : FPrimeStrip V`、`thetaPacket : FiniteThetaPacket l` |
| 我们缺 | `add : AdditiveHodgeTheater`、`mul : MultiplicativeHodgeTheater` 的 Θ±ell/ΘNF 分解；`primeStrips : PrimeStripSystem l`（见 §3）；对称群 `GeoSym l`/`LabCusp l` 字段；`glue`（加法/乘法部分的 l 相等）；Hodge theater 的 histories/link 结构 | — |
| 赋值差异 | 每个 theater 携带完整 `PrimeStripSystem`（addSystem/mulSystem/gaussian/glue） | 我们以单条 `FPrimeStrip` + 有限 thetaPacket 代替整个 system；`thetaPacket` 是实值 q^{j²}，Takkun 的 theta 数据在 `PrimeStripSystem.gaussian`（Mon 内） |

## 3. PrimeStrip 层

| 对象 | Takkun 字段 | 我们字段 | 差异 |
|---|---|---|---|
| PrimeStrip | `Frobenioid/PrimeStrip.lean:22 structure PrimeStrip { loc : V → Model }` + `totalDegree`（对 V 求和、从 Model.degree 读出） | **无对应** | 我们缺 `loc : V → Frobenioid.Model`（每素点局部 Frobenioid 模型）与全局 totalDegree（我们只有 FPrimeStrip.totalDegree 用 degree 字段） |
| DPrimeStrip | `Frobenioid/PrimeStripSystem.lean:38`：`Pi : V→Type`（Group）、`G : V→Type`（Group）、`proj : Π_v →* G_v`、`proj_surjective` | `PrimeStripCore.lean:24`：同四字段 | 字段一致（assignment 相同）；我们缺 `monoAnalytic` 之外的后续层 |
| FPrimeStrip | `PrimeStripSystem.lean:71`：extends D，`Mon : V→Type`（O▷ 非零整数乘法幺半群）、`action : Π_v →* MulAut (Mon v)` | `PrimeStripCore.lean:117`：extends D，`Mon`、`action`、**额外 `degree : Mon_v →* Multiplicative ℝ`** | 赋值差异: 我们 `degree` 是字段；Takkun 的 degree 来自 `PrimeStrip.loc v : Model`（Frobenioid 模型自带 degree），FPrimeStrip 本身无 degree 字段 |
| DhPrimeStrip | `:159`：`G : V→Type` | `PrimeStripCore.lean:49`：`G` | 字段一致 |
| FhPrimeStrip | `:203`：extends Dh，`Mon`（O^× × q_v^N）、`action : G_v →* MulAut Mon` | **无** | 我们缺 F⊢-prime-strip（mono-analytic value monoid q_v^N 与 G_v 作用） |
| GaussianPrimeStrip | `:309`：extends Fh，`qParam : ∀ v, Mon v`；`thetaValueAt : Mon v = gaussianValue (qParam v) j`；`thetaValueAt_neg` | `FiniteThetaPacket`（实值） | 我们缺 Mon 值的 qParam/thetaValue（实值代替幺半群元素） |
| ThetaChain/EtalePicture/FrobeniusChain/LabeledPrimeStripSystem | `:337/:382/:412/:449` | **无** | 我们缺 Θ-link 链、étale picture 的 coricity/spoke 置换、Frobenius 链、labeled 系统/对称作用 |
| PrimeStripSystem | `HodgeTheater/PrimeStripData.lean:85`：V、addSystem（LabCuspPM/GeoSym）、mulSystem（LabCusp/LabCusp）、gaussian、glue | **无** | 这是 Takkun Hodge theater 的核心字段，我们完全缺 |

## 4. LogShell / LogLink / lattice

| 对象 | Takkun 字段 | 我们字段 | 差异 |
|---|---|---|---|
| LogShell | `LogTheta/LogShell.lean:22`：`carrier : Type` [AddCommGroup] | `SourceLogShellCarrier.lean:86 SourceLogShellDatum`：p/hp、K [Field/CharZero]、Units [CommGroup]、invariants : Submonoid、logMap : Units →* Multiplicative K | Takkun 只有载体加法群；我们有 p*_v/preLogShell/logShell 公式 + invariants/unitLayer/codomainKummerContained 具名条件。**两边互缺**: 我们缺 Takkun 的抽象 AddCommGroup 载体与 LogLink/chain；Takkun 缺 pStar/preLogShell/logShell 点集公式 |
| LogLink | `:32`：`logMap : Additive U →+ S.carrier`（U CommGroup） | 我们的 `logMap : Units →* Multiplicative K` | 同内容不同赋值方向（乘→加 vs 乘→Multiplicative）；Takkun 有 LogLink 结构及 logMap_one/mul 律；我们无独立 LogLink |
| LogChain | `:59`：`shell : ℤ → LogShell`、`unit : ℤ → Type` [CommGroup]、`logLink : ∀ m, LogLink (unit m) (shell (m+1))` | **无** | 我们缺 log-link 链（纵向） |
| LogThetaLattice | `Lattice.lean:22`：`HT : ℤ×ℤ → Full`（Hodge theater 格子） | **无**（我们只有 `LogThetaLattice (lattice : Prop) : Prop := lattice` 空壳，按 OWN-ASSETS-A502） | 我们缺 lattice 对象（且不得再以 Prop 恒等充当） |
| LogThetaLatticeConcrete | `LatticeConcrete.lean:31`：core : ℤ×ℤ → DhPrimeStrip、thetaLink（横向 Dh equiv）、unit、shell、logLink（纵向） | **无** | 我们缺 concrete lattice（D⊢ 核 + 横 Θ-link + 纵 log-link） |
| LogShellIndeterminacy | `Indeterminacy.lean:46`：`Γ : Type` [Group]（= (Ind1)×(Ind2)）、`I` [MulAction Γ]、`ind3 : UpperSemiCompatibility Γ I`；`multiradialOutput = orbit` | `Ind1ActionLawsActual`（约 L40-95）：`Ind1TensorAction := polyIso.tensorMap`（label 置换 + 分量线性等价）、`Ind1UnitAction = refl` | **字段差异大**: 我们有 tensor 局的 Ind1 poly-iso 形状但无 Γ 群/Ind2/Ind3/UpperSemiCompatibility；Takkun 有 Γ/Ind3 但未直接对应 tensor packet 的 Ind1 形状 |

## 5. Theta 值

| | Takkun | 我们 |
|---|---|---|
| 值层 | `Theta/ThetaValues.lean:23 gaussExp j = j^2`、`:45 thetaValue (q : M) (j) := q ^ gaussExp j`（M 任意 monoid）、`:74 thetaValueMon`；`GaussianPrimeStrip.thetaValueAt : Mon v` | `FiniteThetaPacket`（`LeanFormal/IUT/IUTII/Theta/FiniteThetaPacket.lean:26`）：`q : ℝ`（>0）、`scale : SignedLabel → ℝ`、`scale_eq : scale j = realThetaValue q j`（实值 q^{j²}）、logVolume |
| 我们缺 | q 在 monoid（如 ℚ̄_pˣ）中的 theta 值、Galois 作用、Kummer 类/根系统；我们只有实值 q^{j²} 与 ± 对称 | — |
| 赋值差异 | Takkun `Mon` 元素值（可落到 ℚ̄_11ˣ 等），实数需取范数/对数；我们直接取 `ℝ` 的 q 与实数幂 | 数值上是范数/对数的复合，需注意与 paper 的 “q_v^{j²} ∈ Mon_v” 的对应 |

## 6. Takkun 有而我们完全没有的具体构造（重大字段级缺口）

- `Arithmetic/RealFrobenioid.lean`: `integralUnits p`（O▷ = 谱范数单位球非零元子幺半群）、`norm_coe_eq_one_of_isUnit`、`degAux/realDeg`（Associates 上 deg=-log‖·‖）、`realFrobenioid p : Frobenioid.Model`（把抽象 Frobenioid 论接到实际 ℚ̄_p 数论）。
- `Arithmetic/RealHodgeTheater.lean`: `RationalPlaces`、`LocalGalois p`（实际 Gal(ℚ̄_p/ℚ_p)）、`galoisUnitsAction`（G_p 在 ℚ̄_pˣ 的实际作用）、`realDStrip`（Π=G=LocalGalois）、`realGaussianStrip`（Mon=ℚ̄_pˣ、qParam=p、thetaValueAt=q^{j²}）、`realPrimeStripSystem l`（Hodge theater 的 PrimeStripSystem 实例）、`realGaussian_nondegenerate`。
- `Arithmetic/RealKummer.lean`: `realQRootSystem`（q 的幂根系）、`realQKummer`/`realQKummer_cocycle`、`realThetaRootSystem`/`realThetaKummer`、`realThetaKummer_cocycle`（theta/Kummer 1-cocycle）、`realSystemKummer`。
- `Frobenioid/PrimeStrip.lean`: `PrimeStrip.loc : V → Frobenioid.Model` + `totalDegree`；`Frobenioid/Basic.lean` 的 `Model`（base/valueMonoid/degree/integral 结构）。
- `LogTheta` 全套（LogShell/LogLink/LogChain/Lattice/LatticeConcrete/LogKummer/Indeterminacy）；`HodgeTheater/PrimeStripData.lean` 的 `PrimeStripSystem`/`LabeledPrimeStripSystem`；`HodgeTheater/Symmetry.lean`；`HodgeTheater/Defs.lean` 的 Additive/Multiplicative/Full 分解。

## 7. 我们相对 Takkun 的额外字段（并非 Takkun 有而我们全缺）

- `SourceLogShellDatum`：`pStar`（p*_v 定义与性质）、`preLogShell`/`logShell` 点集公式、`unitLayer`、`codomainKummerContained`（III Def 1.1(i)/(ii) 的 log 坐标核）；Takkun `LogShell` 只有载体加法群，无此公式层。
- `FPrimeStrip.degree` 作为独立字段（Takkun 从 Model 读）；`InitialThetaArithmeticData` 的 Fmod⊆F⊆K 数域塔结构（Takkun 单域 F + 条件字段）。
- `FiniteThetaPacket` 的实值 q^{j²}/±/logVolume 包（Takkun 在 Mon 元素上定义，需额外取范数才得实数）。
- `SourceProcessionCapsuleData.LogShellFamily.TensorPacket` + `tensorPacketEquiv`（log-shell 张量包分配律，Takkun LogTheta 未必有 tensor packet 的等价证明）——见 OWN-OBJECT-FAITHFULNESS.md §1。

## 8. 结论（只读）

1. 同名字段对照: DPrimeStrip/DhPrimeStrip 两边字段基本一致；我们的 FPrimeStrip 多一个独立 `degree` 字段，但缺 Takkun 的 `loc : V→Frobenioid.Model`（以及 F⊩=F⊢+global realified）。
2. 对象级缺口主要在: Hodge theater 的 Θ±ell/ΘNF 分解 + PrimeStripSystem（addSystem/mulSystem/gaussian/glue/labels/symmetry）；Π 与 G 的 Fh/Gaussian strip 与 Θ-link 链（ThetaChain/EtalePicture/FrobeniusChain）；LogShell/LogLink/LogChain/LogThetaLattice(Concrete)/LogShellIndeterminacy(Γ/Ind3)；ThetaValues 的 monoid 值版本；以及 RealFrobenioid/RealHodgeTheater/RealKummer 全部具体构造。
3. 我们相对 Takkun 的真资产是: pStar/preLogShell/logShell 公式与 invariants/unitLayer 结构、tensor packet 分配律、FPrimeStrip.degree 与数域塔、实值 theta packet、Ind1 poly-iso 形状——对象构造时可与 Takkun 的 Frobenioid/LogShell/lattice/Indeterminacy 字段合并（field-wise merge），但不要再用 Prop/identity 壳。
4. 本文件只读；未改任何文件/队列/watchdog，不新增壳。
